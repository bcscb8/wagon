package exec

import (
	"bytes"
	"fmt"
	"io/ioutil"
	"os"
	"os/exec"
	"runtime/debug"

	"github.com/go-interpreter/wagon/exec/internal/compile"
	"github.com/go-interpreter/wagon/wasm"
	ops "github.com/go-interpreter/wagon/wasm/operators"
)

const (
	FUNCTION_PREFIX = "wfun_"
	LOCAL_PREFIX    = "lc"
	VARIABLE_PREFIX = "v"
	LABEL_PREFIX    = "L_"
)

var (
	log wasm.Logger
)

// SetCGenLogger --
func SetCGenLogger(l wasm.Logger) {
	log = l
}

// CGenContext --
type CGenContext struct {
	vm            *VM
	names         []string
	mainIndex     int
	mainName      string
	keepCSource   bool
	disableGas    bool
	enableComment bool

	f            compiledFunction
	fsig         wasm.FunctionSig
	id           uint64
	insMetas     []compile.InstructionMetadata
	branchTables []*compile.BranchTable
	labelTables  map[int]compile.Label
	labelStacks  map[int][]int

	pc      int
	opCount int
	varn    int
	stack   []int
	calln   int

	buf  *bytes.Buffer
	tabs int
}

// NewCGenContext --
func NewCGenContext(vm *VM, keepSource bool) *CGenContext {
	g := CGenContext{
		vm:          vm,
		mainIndex:   -1,
		mainName:    "thunderchain_main",
		labelStacks: make(map[int][]int),
		keepCSource: keepSource,

		stack: make([]int, 0, 1024),
		buf:   bytes.NewBuffer(nil),
	}

	return &g
}

// DisableGas --
func (g *CGenContext) DisableGas(s bool) {
	g.disableGas = s
}

// EnableComment --
func (g *CGenContext) EnableComment(s bool) {
	g.enableComment = s
}

func (g *CGenContext) resetF(f compiledFunction, id uint64) {
	g.f = f
	g.id = id
	g.insMetas = f.codeMeta.Instructions
	g.branchTables = f.codeMeta.BranchTables
	g.labelTables = f.codeMeta.LabelTables
	g.labelStacks = make(map[int][]int)

	g.pc = 0
	g.opCount = 0
	g.varn = 0
	// g.stack = g.stack[:0]
	g.stack = make([]int, 0, f.maxDepth)
	g.calln = 0

	g.buf.Reset()
	g.tabs = 0

	tIndex := g.vm.module.Function.Types[g.id]
	g.fsig = g.vm.module.Types.Entries[tIndex]
}

func (g *CGenContext) putTabs() {
	for i := 0; i < g.tabs; i++ {
		g.buf.WriteString("\t")
	}
}

func (g *CGenContext) sprintf(format string, args ...interface{}) {
	g.putTabs()
	g.buf.WriteString(fmt.Sprintf(format, args...))
}

func (g *CGenContext) writes(s string) {
	g.putTabs()
	g.buf.WriteString(s)
}

func (g *CGenContext) writeln(s string) {
	g.putTabs()
	g.buf.WriteString(s)
	g.buf.WriteString("\n")
}

func (g *CGenContext) cbytes() []byte {
	b := g.buf.Bytes()
	return b
}

func (g *CGenContext) pushStack(x int) {
	g.stack = append(g.stack, x)
	if x >= g.varn {
		g.sprintf("value_t %s%d; %s%d.vu64 = 0;\n", VARIABLE_PREFIX, x, VARIABLE_PREFIX, x)
		g.varn++
	}
}

func (g *CGenContext) popStack() int {
	x := g.topStack()
	g.stack = g.stack[:len(g.stack)-1]
	return x
}

func (g *CGenContext) topStack() int {
	return g.stack[len(g.stack)-1]
}

func (g *CGenContext) discardStack(n int) {
	g.stack = g.stack[:len(g.stack)-n]
}

func (g *CGenContext) lenStack() int {
	return len(g.stack)
}

func (g *CGenContext) isEnd() bool {
	return g.pc == len(g.f.code)
}

func (g *CGenContext) op() byte {
	if label, ok := g.labelTables[g.pc]; ok {
		// write label
		flag := false
		if g.tabs > 0 {
			g.tabs--
			flag = true
		}
		g.sprintf("\n%s%d:\n", LABEL_PREFIX, label.Index)
		if flag {
			g.tabs++
		}
		if g.disableGas {
			g.writeln("_dummy++;")
		}

		// change stack
		if tmpStack, ok := g.labelStacks[g.pc]; ok {
			log.Printf("change stack: pc:%d, new_stack:%v, old_stack:%v", g.pc, tmpStack, g.stack)
			g.stack = tmpStack
		} else {
			log.Printf("No change stack: pc:%d", g.pc)
		}
	}

	ins := g.f.code[g.pc]
	g.pc++

	if ins != ops.Call && ins != ops.GrowMemory {
		var err error
		cost := GasQuickStep

		switch ins {
		case ops.Return:
			cost = 0
		case compile.OpJmp, compile.OpJmpZ, compile.OpJmpNz, ops.BrTable, compile.OpDiscard, compile.OpDiscardPreserveTop, ops.WagonNativeExec:
			cost = GasQuickStep
		default:
			gasCost := g.vm.opSet[ins].gasCost
			cost, err = gasCost(g.vm)
			if err != nil {
				cost = GasQuickStep
				panic(fmt.Sprintf("gasCost fail: op:0x%x %s", ins, ops.OpSignature(ins)))
			}
		}
		g.genGasChecker(ins, cost)
	}

	g.opCount++
	return ins
}

func (g *CGenContext) genGasChecker(op byte, cost uint64) {
	if !g.disableGas {
		if g.enableComment {
			g.writeln(fmt.Sprintf("// %d:%d, %s", g.pc, g.opCount, ops.OpSignature(op)))
		}
		// g.writeln(fmt.Sprintf("vm->gas_used += %d; if (unlikely(vm->gas_used > vm->gas)) { vm->gas_used -= %d; panic(vm, \"OutOfGas\"); }", cost, cost))
		g.writeln(fmt.Sprintf("if (likely(vm->gas >= %d)) {vm->gas -= %d; vm->gas_used += %d;} else {panic(vm, \"OutOfGas\");}", cost, cost, cost))
		// g.writeln(fmt.Sprintf("if (likely(vm->gas >= vm->gas_used) && likely((vm->gas - vm->gas_used) >= %d)) { vm->gas_used += %d; } else { panic(vm, \"OutOfGas\"); }", cost, cost))
		// g.writeln(fmt.Sprintf("printf(\"op:%s, gas:%d\\n\");", ops.OpSignature(op), cost))
	}
}

func (g *CGenContext) fetchUint32() uint32 {
	v := endianess.Uint32(g.f.code[g.pc:])
	g.pc += 4
	return v
}

func (g *CGenContext) fetchUint64() uint64 {
	v := endianess.Uint64(g.f.code[g.pc:])
	g.pc += 8
	return v
}

func (g *CGenContext) fetchInt64() int64 {
	return int64(g.fetchUint64())
}

func (g *CGenContext) fetchBool() bool {
	return g.fetchInt8() != 0
}

func (g *CGenContext) fetchInt8() int8 {
	i := int8(g.f.code[g.pc])
	g.pc++
	return i
}

var (
	cbasic = `
// Auto Generate. Do Not Edit.

#include <stdint.h>
#include <string.h>
#include <stdlib.h>

typedef struct {
	void *ctx;
	uint64_t gas;
	uint64_t gas_used;
	int32_t pages;
	uint8_t *mem;
} vm_t;

extern uint64_t GoFunc(vm_t*, const char*, int32_t, uint64_t*);
extern void GoPanic(vm_t*, const char*);
extern void GoRevert(vm_t*, const char*);
extern void GoExit(vm_t*, int32_t);
extern void GoGrowMemory(vm_t*, int32_t);

static inline void panic(vm_t *vm, const char *msg) {
	GoPanic(vm, msg);
}

typedef union value {
	uint64_t 	vu64;
	int64_t 	vi64;
	uint32_t 	vu32;
	int32_t 	vi32;
	uint16_t 	vu16;
	int16_t 	vi16;
	uint8_t 	vu8;
	int8_t 		vi8;
} value_t;

#define likely(x)       __builtin_expect((x),1)
#define unlikely(x)     __builtin_expect((x),0)

static inline uint64_t clz32(uint32_t x) {
	return __builtin_clz(x);
}
static inline uint64_t ctz32(uint32_t x) {
	return __builtin_ctz(x);
}
static inline uint64_t clz64(uint64_t x) {
	return __builtin_clzll(x);
}
static inline uint64_t ctz64(uint64_t x) {
	return __builtin_ctzll(x);
}
static inline uint64_t rotl32(uint32_t x, uint32_t r) {
	return (x << r) | (x >> (32 - r % 32));
}
static inline uint64_t rotl64(uint64_t x, uint64_t r) {
	return (x << r) | (x >> (64 - r % 64));
}
static inline uint64_t rotr32(uint32_t x, uint32_t r) {
	return (x >> r) | (x << (32 - r % 32));
}
static inline uint64_t rotr64(uint64_t x, uint64_t r) {
	return (x >> r) | (x << (64 - r % 64));
}
static inline uint32_t popcnt32(uint32_t x) {
	return (uint32_t)(__builtin_popcountl(x));
}
static inline uint32_t popcnt64(uint64_t x) {
	return (uint32_t)(__builtin_popcountll(x));
}

`
	cenv = `
// -----------------------------------------------------
//  env api wrapper

static const uint64_t MAX_U64 = (uint64_t)(-1);
static const uint32_t MAX_U32 = (uint32_t)(-1);

#ifdef ENABLE_GAS

static inline uint32_t to_word_size(uint32_t n) {
	if (n > (MAX_U32 - 31))
		return ((MAX_U32 >> 5) + 1);
	return ((n + 31) >> 5);
}

#define USE_MEM_GAS_N(vm, n, step) {\
	uint64_t cost = to_word_size(n) * step + 2;\
	if (likely(vm->gas >= cost)) {\
		vm->gas -= cost;\
		vm->gas_used += cost;\
	} else {\
		panic(vm, "OutOfGas");\
	}\
}

#define USE_SIM_GAS_N(vm, n) {\
	uint64_t cost = n;\
	if (likely(vm->gas >= cost)) {\
		vm->gas -= cost;\
		vm->gas_used += cost;\
	} else {\
		panic(vm, "OutOfGas");\
	}\
}

#else
#define USE_MEM_GAS_N(vm, n, step) 
#define USE_SIM_GAS_N(vm, n) 
#endif

static inline uint32_t TCMemcpy(vm_t *vm, uint32_t dst, uint32_t src, uint32_t n) {
	USE_MEM_GAS_N(vm, n, 3)
	memcpy(vm->mem+dst, vm->mem+src, n);
	return dst;
}

static inline uint32_t TCMemset(vm_t *vm, uint32_t src, int c, uint32_t n) {
	USE_MEM_GAS_N(vm, n, 3)
	memset(vm->mem+src, c, n);
	return src;
}

static inline uint32_t TCMemmove(vm_t *vm, uint32_t dst, uint32_t src, uint32_t n) {
	USE_MEM_GAS_N(vm, n, 3)
	memmove(vm->mem+dst, vm->mem+src, n);
	return dst;
}

static inline int TCMemcmp(vm_t *vm, uint32_t s1, uint32_t s2, uint32_t n) {
	USE_MEM_GAS_N(vm, n, 1)
	return memcmp(vm->mem+s1, vm->mem+s2, n);
}

static inline int TCStrcmp(vm_t *vm, uint32_t s1, uint32_t s2) {
	uint32_t n1 = strlen(vm->mem+s1);
	uint32_t n2 = strlen(vm->mem+s2);
	uint32_t n = (n1 > n2) ? n1 : n2;
	USE_MEM_GAS_N(vm, n, 1)
	return strcmp(vm->mem+s1, vm->mem+s2);
}

static inline uint32_t TCStrcpy(vm_t *vm, uint32_t dst, uint32_t src) {
	uint32_t n = strlen(vm->mem+src);
	USE_MEM_GAS_N(vm, n, 3)
	strcpy(vm->mem+dst, vm->mem+src);
	return dst;
}

static inline uint32_t TCStrlen(vm_t *vm, uint32_t s) {
	USE_SIM_GAS_N(vm, 2)
	return strlen(vm->mem + s);
}

static inline int TCAtoi(vm_t *vm, uint32_t s) {
	USE_SIM_GAS_N(vm, 20)
	return atoi(vm->mem+s);
}

static inline int64_t TCAtoi64(vm_t *vm, uint32_t s) {
	USE_SIM_GAS_N(vm, 20)
	return atoll(vm->mem + s);
}

// TCRequire
static inline void TCAssert(vm_t *vm, int32_t cond) {
	USE_SIM_GAS_N(vm, 2)
	if (cond == 0) {
		GoRevert(vm, "");
	}
}

// TCRequireWithMsg
static inline void TCAssertWithMsg(vm_t *vm, int32_t cond, uint32_t msg) {
	uint32_t n = strlen(vm->mem+msg);
	USE_MEM_GAS_N(vm, n, 1)
	if (cond == 0) {
		GoRevert(vm, vm->mem+msg);
	}
}

`
)

// Compile --
func (g *CGenContext) Compile(code []byte, path, name string) (string, error) {
	os.MkdirAll(path, os.ModeDir)
	in := fmt.Sprintf("%s/%s.c", path, name)
	out := fmt.Sprintf("%s/%s.so", path, name)

	if err := ioutil.WriteFile(in, code, 0644); err != nil {
		log.Printf("WriteFile %s fail: %s", in, err)
		return "", err
	}

	if !g.keepCSource {
		defer func() {
			os.Remove(in)
		}()
	}

	cmd := exec.Command("gcc", "-fPIC", "-O3", "-shared", "-o", out, in)
	cmdOut, err := cmd.CombinedOutput()
	log.Printf("compiler output: %s", string(cmdOut))
	return out, err
}

// Generate --
func (g *CGenContext) Generate() ([]byte, error) {
	buf := bytes.NewBuffer(nil)

	// header
	buf.WriteString(cbasic)
	if !g.disableGas {
		buf.WriteString("\n#define ENABLE_GAS\n\n")
	}
	buf.WriteString(cenv)
	buf.WriteString("\n//--------------------------\n\n")

	for index, f := range g.vm.funcs {
		name := g.vm.module.FunctionIndexSpace[index]
		if _, ok := f.(goFunction); ok {
			log.Printf("[Generate] goFunction: index:%d, name:%s", index, name)
		} else {
			log.Printf("[Generate] localFunction: index:%d, name:%s", index, name)
		}
	}

	if g.vm.module.Import != nil {
		for index, entry := range g.vm.module.Import.Entries {
			log.Printf("[Generate] Import: index:%d, entry:%s", index, entry)
		}
	}

	if g.vm.module.Export != nil {
		for name, entry := range g.vm.module.Export.Entries {
			log.Printf("[Generate] Export: name:%s, entry:%s", name, entry.String())
		}
	}

	// function declation
	names := make([]string, 0, len(g.vm.funcs))
	module := g.vm.module
	for index, f := range g.vm.funcs {
		if _, ok := f.(goFunction); ok {
			name := module.FunctionIndexSpace[index].Name
			if name == "" {
				log.Printf("[Generate] goFunction without name: func_index:%d", index)
				return buf.Bytes(), fmt.Errorf("goFunction without name")
			}
			names = append(names, name)
			continue
		}

		if module.FunctionIndexSpace[index].Name == g.mainName {
			g.mainIndex = index
			log.Printf("skip thunderchain_main: index=%d", index)
			continue
		}
		log.Printf("[Generate] declation: %s", module.FunctionIndexSpace[index].Name)

		tIndex := module.Function.Types[index]
		fsig := module.Types.Entries[tIndex]

		buf.WriteString("static ")
		if len(fsig.ReturnTypes) > 0 {
			switch fsig.ReturnTypes[0] {
			case wasm.ValueTypeI32:
				buf.WriteString("uint32_t ")
			case wasm.ValueTypeI64:
				buf.WriteString("uint64_t ")
			default:
				log.Printf("[Generate] invalid return_type(%s): func_index:%d", fsig.ReturnTypes[0].String(), index)
				return buf.Bytes(), fmt.Errorf("invalid return type")
			}
		} else {
			buf.WriteString("void ")
		}
		buf.WriteString(fmt.Sprintf("%s%d(vm_t*", FUNCTION_PREFIX, index))

		for argIndex, argType := range fsig.ParamTypes {
			vtype := ""
			switch argType {
			case wasm.ValueTypeI32:
				vtype = "uint32_t"
			case wasm.ValueTypeI64:
				vtype = "uint64_t"
			default:
				log.Printf("[Generate] invalid param_type(%s): func_index:%d, param_index:%d", argType.String(), index, argIndex)
				return buf.Bytes(), fmt.Errorf("invalid params type")
			}
			buf.WriteString(fmt.Sprintf(", %s", vtype))
		}
		buf.WriteString(");\n")
	}

	g.names = names
	// static const char *env_func_names[] = {"", ""};
	buf.WriteString("\nstatic const char *env_func_names[] = {")
	for index, name := range names {
		if index > 0 {
			buf.WriteString(", ")
		}
		buf.WriteString(fmt.Sprintf("\"%s\"", name))
	}
	buf.WriteString("};\n")
	buf.WriteString("\n//--------------------------\n\n")

	// function code
	for index, f := range g.vm.funcs {
		cf, ok := f.(compiledFunction)
		if ok {
			g.resetF(cf, uint64(index))
			code, err := g.doGenerateF()
			if err != nil {
				return buf.Bytes(), err
			}
			buf.Write(code)
		}
	}

	return buf.Bytes(), nil
}

func (g *CGenContext) doGenerateF() (_ []byte, err error) {
	defer func() {
		if r := recover(); r != nil {
			log.Printf("panic: %s", string(debug.Stack()))

			switch e := r.(type) {
			case error:
				err = e
			default:
				err = fmt.Errorf("panic: %v", e)
			}
		}
	}()

	funcName := g.mainName
	if g.id != uint64(g.mainIndex) {
		funcName = fmt.Sprintf("%s%d", FUNCTION_PREFIX, g.id)
	}

	fsig := g.fsig
	if len(fsig.ReturnTypes) > 0 {
		switch fsig.ReturnTypes[0] {
		case wasm.ValueTypeI32:
			g.sprintf("uint32_t %s(vm_t *vm", funcName)
		case wasm.ValueTypeI64:
			g.sprintf("uint64_t %s(vm_t *vm", funcName)
		default:
			panic("invalid return type")
		}
	} else {
		g.sprintf("void %s(vm_t *vm", funcName)
	}

	for argIndex, argType := range fsig.ParamTypes {
		vtype := ""
		switch argType {
		case wasm.ValueTypeI32:
			vtype = "uint32_t"
		case wasm.ValueTypeI64:
			vtype = "uint64_t"
		default:
			panic("invalid params type")
		}
		g.sprintf(",%s %s%d", vtype, LOCAL_PREFIX, argIndex)
	}
	g.writes(") {\n")
	g.tabs++

	// generate locals
	for i := g.f.args; i < g.f.totalLocalVars; i++ {
		g.sprintf("uint64_t %s%d = 0;\n", LOCAL_PREFIX, i)
	}
	if g.disableGas {
		g.writeln("uint8_t _dummy = 0;\n")
	}

	// generate code body
	var op byte
	for !g.isEnd() {
		op = g.op()
		log.Printf("Generate [%d:%d] op: %s", g.pc, len(g.f.code), ops.OpSignature(op))
		switch op {
		case ops.Nop:
		case ops.Drop:
			g.popStack()
		case ops.Unreachable:
			g.sprintf("panic(vm, \"Unreachable\");")
		case compile.OpJmp, compile.OpJmpNz, compile.OpJmpZ, ops.BrTable:
			genJmpOp(g, op)
		// case ops.CallIndirect: // @Todo???
		case ops.Call:
			err = genCallOp(g, op)
		case compile.OpDiscard:
			n := g.fetchUint32()
			g.discardStack(int(n))
		case compile.OpDiscardPreserveTop:
			top := g.topStack()
			n := g.fetchUint32()
			g.discardStack(int(n))
			g.pushStack(top)
		case ops.Return:
			genReturnOp(g, op)
		case ops.Select:
			genSelectOp(g, op)
		case ops.CurrentMemory, ops.GrowMemory:
			genMemoryOp(g, op)
		case ops.GetLocal, ops.SetLocal, ops.TeeLocal:
			genLocalOp(g, op)
		case ops.GetGlobal, ops.SetGlobal:
			genGlobalOp(g, op)
		case ops.I32Const, ops.I64Const:
			genConstOp(g, op)
		case ops.I32Add, ops.I32Sub, ops.I32Mul, ops.I32DivU, ops.I32RemU, ops.I32DivS, ops.I32RemS,
			ops.I32And, ops.I32Or, ops.I32Xor,
			ops.I32Shl, ops.I32ShrS, ops.I32ShrU,
			ops.I32LeS, ops.I32LeU, ops.I32LtS, ops.I32LtU, ops.I32GeS, ops.I32GeU, ops.I32GtS, ops.I32GtU, ops.I32Eq, ops.I32Ne:
			genI32BinOp(g, op)
		case ops.I64Add, ops.I64Sub, ops.I64Mul, ops.I64DivS, ops.I64DivU, ops.I64RemS, ops.I64RemU,
			ops.I64And, ops.I64Or, ops.I64Xor,
			ops.I64Shl, ops.I64ShrS, ops.I64ShrU,
			ops.I64LeS, ops.I64LeU, ops.I64LtS, ops.I64LtU, ops.I64GeS, ops.I64GeU, ops.I64GtS, ops.I64GtU, ops.I64Eq, ops.I64Ne:
			genI64BinOp(g, op)
		case ops.I32Rotl, ops.I32Rotr, ops.I64Rotl, ops.I64Rotr:
			genBinFuncOp(g, op)
		case ops.I32Eqz, ops.I64Eqz:
			genEqzOp(g, op)
		case ops.I32Clz, ops.I32Ctz, ops.I64Clz, ops.I64Ctz, ops.I32Popcnt, ops.I64Popcnt:
			genUnFuncOp(g, op)
		case ops.I32WrapI64, ops.I64ExtendSI32, ops.I64ExtendUI32:
			genConvertOp(g, op)
		case ops.I64Load, ops.I64Load32s, ops.I64Load32u, ops.I64Load16s, ops.I64Load16u, ops.I64Load8s, ops.I64Load8u,
			ops.I32Load, ops.I32Load16s, ops.I32Load16u, ops.I32Load8s, ops.I32Load8u:
			genLoadOp(g, op)
		case ops.I64Store, ops.I64Store32, ops.I64Store16, ops.I64Store8,
			ops.I32Store, ops.I32Store16, ops.I32Store8:
			genStoreOp(g, op)
		default:
			err = fmt.Errorf("Not Support op(0x%x): %s", op, ops.OpSignature(op))
		}

		if err != nil {
			return g.cbytes(), err
		}
	}

	if op != ops.Return {
		genReturnOp(g, ops.Return)
	} else {
		log.Printf("last op is ops.Return")
	}
	g.tabs--
	g.writes("}\n\n")

	return g.cbytes(), nil
}

// --------------------------------------------------------

func genReturnOp(g *CGenContext, op byte) {
	var buf string
	if g.f.returns {
		switch g.fsig.ReturnTypes[0] {
		case wasm.ValueTypeI32:
			buf = fmt.Sprintf("return %s%d.vu32;", VARIABLE_PREFIX, g.popStack())
		case wasm.ValueTypeI64:
			buf = fmt.Sprintf("return %s%d.vu64;", VARIABLE_PREFIX, g.popStack())
		}
	} else {
		buf = "return;"
	}

	g.writeln(buf)
	log.Printf("[genReturnOp] op:0x%x, %s", op, buf)
}

func genLocalOp(g *CGenContext, op byte) {
	index := g.fetchUint32()
	var buf string

	switch op {
	case ops.GetLocal:
		g.pushStack(g.varn)
		buf = fmt.Sprintf("%s%d.vu64 = %s%d;", VARIABLE_PREFIX, g.topStack(), LOCAL_PREFIX, index)
	case ops.SetLocal:
		buf = fmt.Sprintf("%s%d = %s%d.vu64;", LOCAL_PREFIX, index, VARIABLE_PREFIX, g.popStack())
	case ops.TeeLocal:
		buf = fmt.Sprintf("%s%d = %s%d.vu64;", LOCAL_PREFIX, index, VARIABLE_PREFIX, g.topStack())
	}

	g.writeln(buf)
	log.Printf("[genLocalOp] op:0x%x, %s", op, buf)
}

func genGlobalOp(g *CGenContext, op byte) {
	index := g.fetchUint32()
	var buf string

	switch op {
	case ops.GetGlobal:
		g.pushStack(g.varn)
		buf = fmt.Sprintf("%s%d.vu64 = globals[%d];", VARIABLE_PREFIX, g.topStack(), index)
	case ops.SetGlobal:
		buf = fmt.Sprintf("globals[%d] = %s%d.vu64;", index, VARIABLE_PREFIX, g.popStack())
	}

	g.writeln(buf)
	log.Printf("[genGlocalOp] op:0x%x, %s", op, buf)
}

func genConstOp(g *CGenContext, op byte) {
	var buf string

	g.pushStack(g.varn)
	switch op {
	case ops.I32Const:
		val := g.fetchUint32()
		buf = fmt.Sprintf("%s%d.vu32 = %d;", VARIABLE_PREFIX, g.topStack(), val)
	case ops.I64Const:
		val := g.fetchUint64()
		buf = fmt.Sprintf("%s%d.vu64 = %d;", VARIABLE_PREFIX, g.topStack(), val)
	}

	g.writeln(buf)
	log.Printf("[genConstOp] op:0x%x, %s", op, buf)
}

func genSelectOp(g *CGenContext, op byte) {
	g.pushStack(g.varn)

	v := g.popStack()
	cond := g.popStack()
	v2 := g.popStack()
	v1 := g.popStack()
	buf := fmt.Sprintf("%s%d = %s%d.vu32 ? %s%d : %s%d;", VARIABLE_PREFIX, v,
		VARIABLE_PREFIX, cond,
		VARIABLE_PREFIX, v1,
		VARIABLE_PREFIX, v2)
	g.writeln(buf)
	g.pushStack(v)

	log.Printf("[genSelectOp] op:0x%x, %s", op, buf)
}

func genEqzOp(g *CGenContext, op byte) {
	var buf string

	g.pushStack(g.varn)
	x := g.popStack()
	a := g.popStack()
	switch op {
	case ops.I32Eqz:
		buf = fmt.Sprintf("%s%d.vi32 = (%s%d.vu32 == 0);", VARIABLE_PREFIX, x, VARIABLE_PREFIX, a)
	case ops.I64Eqz:
		buf = fmt.Sprintf("%s%d.vi64 = (%s%d.vu64 == 0);", VARIABLE_PREFIX, x, VARIABLE_PREFIX, a)
	}
	g.writeln(buf)
	g.pushStack(x)

	log.Printf("[genEqzOp] op:0x%x, %s", op, buf)
}

func genI32BinOp(g *CGenContext, op byte) {
	opStr := ""
	vtype := "vu32"

	switch op {
	case ops.I32Add:
		opStr = "+"
	case ops.I32Sub:
		opStr = "-"
	case ops.I32Mul:
		opStr = "*"
	case ops.I32DivU:
		opStr = "/"
	case ops.I32RemU:
		opStr = "%"
	case ops.I32DivS:
		opStr = "/"
		vtype = "vi32"
	case ops.I32RemS:
		opStr = "%"
		vtype = "vi32"
	case ops.I32And:
		opStr = "&"
	case ops.I32Or:
		opStr = "|"
	case ops.I32Xor:
		opStr = "^"
	case ops.I32Shl:
		opStr = "<<"
	case ops.I32ShrU:
		opStr = ">>"
	case ops.I32ShrS:
		opStr = ">>"
		vtype = "vi32"
	case ops.I32LeS:
		opStr = "<="
		vtype = "vi32"
	case ops.I32LeU:
		opStr = "<="
	case ops.I32LtS:
		opStr = "<"
		vtype = "vi32"
	case ops.I32LtU:
		opStr = "<"
	case ops.I32GeS:
		opStr = ">="
		vtype = "vi32"
	case ops.I32GeU:
		opStr = ">="
	case ops.I32GtS:
		opStr = ">"
		vtype = "vi32"
	case ops.I32GtU:
		opStr = ">"
	case ops.I32Eq:
		opStr = "=="
	case ops.I32Ne:
		opStr = "!="
	default:
		panic(fmt.Sprintf("[genI32BinOp] invalid op: 0x%x", op))
	}

	// c = a op b

	// push c: a -> b -> c
	g.pushStack(g.varn)

	c := g.popStack()
	b := g.popStack()
	a := g.popStack()

	if opStr == "/" || opStr == "%" {
		g.sprintf("if (unlikely(%s%d.%s == 0)) { panic(vm, \"DivZero\"); }\n", VARIABLE_PREFIX, b, vtype)
	}
	buf := fmt.Sprintf("%s%d.%s = (%s%d.%s %s %s%d.%s);", VARIABLE_PREFIX, c, vtype,
		VARIABLE_PREFIX, a, vtype,
		opStr,
		VARIABLE_PREFIX, b, vtype)
	g.writeln(buf)
	g.pushStack(c)

	log.Printf("[genI32BinOp] op:0x%x, %s", op, buf)
}

func genI64BinOp(g *CGenContext, op byte) {
	opStr := ""
	vtype := "vu64"

	switch op {
	case ops.I64Add:
		opStr = "+"
	case ops.I64Sub:
		opStr = "-"
	case ops.I64Mul:
		opStr = "*"
	case ops.I64DivU:
		opStr = "/"
	case ops.I64RemU:
		opStr = "%"
	case ops.I64DivS:
		opStr = "/"
		vtype = "vi64"
	case ops.I64RemS:
		opStr = "%"
		vtype = "vi64"
	case ops.I64And:
		opStr = "&"
	case ops.I64Or:
		opStr = "|"
	case ops.I64Xor:
		opStr = "^"
	case ops.I64Shl:
		opStr = "<<"
	case ops.I64ShrU:
		opStr = ">>"
	case ops.I64ShrS:
		opStr = ">>"
		vtype = "vi64"
	case ops.I64LeS:
		opStr = "<="
		vtype = "vi64"
	case ops.I64LeU:
		opStr = "<="
	case ops.I64LtS:
		opStr = "<"
		vtype = "vi64"
	case ops.I64LtU:
		opStr = "<"
	case ops.I64GeS:
		opStr = ">="
		vtype = "vi64"
	case ops.I64GeU:
		opStr = ">="
	case ops.I64GtS:
		opStr = ">"
		vtype = "vi64"
	case ops.I64GtU:
		opStr = ">"
	case ops.I64Eq:
		opStr = "=="
	case ops.I64Ne:
		opStr = "!="
	default:
		panic(fmt.Sprintf("[genI64BinOp] invalid op: 0x%x", op))
	}

	g.pushStack(g.varn)
	c := g.popStack()
	b := g.popStack()
	a := g.popStack()

	if opStr == "/" || opStr == "%" {
		g.sprintf("if (unlikely(%s%d.%s == 0)) { panic(vm, \"DivZero\"); }", VARIABLE_PREFIX, b, vtype)
	}
	buf := fmt.Sprintf("%s%d.%s = (%s%d.%s %s %s%d.%s);", VARIABLE_PREFIX, c, vtype,
		VARIABLE_PREFIX, a, vtype,
		opStr,
		VARIABLE_PREFIX, b, vtype)
	g.writeln(buf)
	g.pushStack(c)

	log.Printf("[genI64BinOp] op:0x%x, %s", op, buf)
}

func genBinFuncOp(g *CGenContext, op byte) {
	fName := ""
	vtype := "vu32"

	switch op {
	case ops.I32Rotl:
		fName = "rotl32"
	case ops.I32Rotr:
		fName = "rotr32"
	case ops.I64Rotl:
		fName = "rotl64"
		vtype = "vu64"
	case ops.I64Rotr:
		fName = "rotr64"
		vtype = "vu64"
	default:
		panic(fmt.Sprintf("[genBinFuncOp] invalid op: 0x%x", op))
	}

	// c = f(a, b);
	// push c: a -> b -> c
	g.pushStack(g.varn)
	c := g.popStack()
	b := g.popStack()
	a := g.popStack()
	buf := fmt.Sprintf("%s%d.%s = %s(%s%d.%s, %s%d.%s);", VARIABLE_PREFIX, c, vtype,
		fName,
		VARIABLE_PREFIX, a, vtype,
		VARIABLE_PREFIX, b, vtype)
	g.writeln(buf)
	g.pushStack(c)

	log.Printf("[genBinFuncOp] op:0x%x, %s", op, buf)
}

func genUnFuncOp(g *CGenContext, op byte) {
	fName := ""
	vtype := "vu32"

	switch op {
	case ops.I32Clz:
		fName = "clz32"
	case ops.I32Ctz:
		fName = "ctz32"
	case ops.I32Popcnt:
		fName = "popcnt32"
	case ops.I64Clz:
		fName = "clz64"
		vtype = "vu64"
	case ops.I64Ctz:
		fName = "ctz64"
		vtype = "vu64"
	case ops.I64Popcnt:
		fName = "popcnt64"
		vtype = "vu64"
	default:
		panic(fmt.Sprintf("[genUnFuncOp] invalid op: 0x%x", op))
	}

	g.pushStack(g.varn)
	c := g.popStack()
	a := g.popStack()
	buf := fmt.Sprintf("%s%d.%s = %s(%s%d.%s);", VARIABLE_PREFIX, c, vtype,
		fName,
		VARIABLE_PREFIX, a, vtype)
	g.writeln(buf)
	g.pushStack(c)

	log.Printf("[genUnFuncOp] op:0x%x, %s", op, buf)
}

func genConvertOp(g *CGenContext, op byte) {
	dstType := ""
	srcType := ""

	switch op {
	case ops.I32WrapI64:
		srcType = "vu64"
		dstType = "vu32"
	case ops.I64ExtendSI32:
		srcType = "vi32"
		dstType = "vi64"
	case ops.I64ExtendUI32:
		srcType = "vu32"
		dstType = "vu64"
	default:
		panic(fmt.Sprintf("[genConvertOp] invalid op: 0x%x", op))
	}

	x := g.popStack()
	buf := fmt.Sprintf("%s%d.%s = (%s)(%s%d.%s);", VARIABLE_PREFIX, x, dstType,
		dstType,
		VARIABLE_PREFIX, x, srcType)
	g.writeln(buf)
	g.pushStack(x)

	log.Printf("[genConvertOp] op:0x%x, %s", op, buf)
}

func genLoadOp(g *CGenContext, op byte) {
	vtype := ""
	dataType := ""
	_type := ""

	switch op {
	case ops.I64Load:
		vtype = "vu64"
		_type = "uint64_t"
		dataType = "uint64_t"
	case ops.I64Load32s:
		vtype = "vi64"
		_type = "int64_t"
		dataType = "int32_t"
	case ops.I64Load32u:
		vtype = "vu64"
		_type = "uint64_t"
		dataType = "uint32_t"
	case ops.I64Load16s:
		vtype = "vi64"
		_type = "int64_t"
		dataType = "int16_t"
	case ops.I64Load16u:
		vtype = "vu64"
		_type = "uint64_t"
		dataType = "uint16_t"
	case ops.I64Load8s:
		vtype = "vi64"
		_type = "int64_t"
		dataType = "int8_t"
	case ops.I64Load8u:
		vtype = "vi64"
		_type = "uint64_t"
		dataType = "int8_t"
	case ops.I32Load:
		vtype = "vu32"
		_type = "uint32_t"
		dataType = "uint32_t"
	case ops.I32Load16s:
		vtype = "vi32"
		_type = "int32_t"
		dataType = "int16_t"
	case ops.I32Load16u:
		vtype = "vu32"
		_type = "uint32_t"
		dataType = "uint16_t"
	case ops.I32Load8s:
		vtype = "vi32"
		_type = "int32_t"
		dataType = "int8_t"
	case ops.I32Load8u:
		vtype = "vu32"
		_type = "uint32_t"
		dataType = "uint8_t"
	default:
		panic(fmt.Sprintf("[genLoadOp] invalid op: 0x%x", op))
	}

	g.pushStack(g.varn)

	v := g.popStack()
	offset := g.popStack()
	buf := fmt.Sprintf("%s%d.%s = (%s)(*((%s *)(vm->mem + %du + %s%d.vu32)));", VARIABLE_PREFIX, v, vtype, _type,
		dataType,
		g.fetchUint32(),
		VARIABLE_PREFIX, offset)
	g.writeln(buf)
	g.pushStack(v)

	log.Printf("[genLoadOp] op:0x%x, %s", op, buf)
}

func genStoreOp(g *CGenContext, op byte) {
	vtype := ""
	dataType := ""

	switch op {
	case ops.I64Store:
		vtype = "vu64"
		dataType = "uint64_t"
	case ops.I64Store32:
		vtype = "vu32"
		dataType = "uint32_t"
	case ops.I64Store16:
		vtype = "vu16"
		dataType = "uint16_t"
	case ops.I64Store8:
		vtype = "vu8"
		dataType = "uint8_t"
	case ops.I32Store:
		vtype = "vu32"
		dataType = "uint32_t"
	case ops.I32Store16:
		vtype = "vu16"
		dataType = "uint16_t"
	case ops.I32Store8:
		vtype = "vu8"
		dataType = "uint8_t"
	default:
		panic(fmt.Sprintf("[genStoreOp] invalid op: 0x%x", op))
	}

	v := g.popStack()
	offset := g.popStack()
	buf := fmt.Sprintf("(*((%s *)(vm->mem + %du + %s%d.vu32))) = %s%d.%s;", dataType,
		g.fetchUint32(),
		VARIABLE_PREFIX, offset,
		VARIABLE_PREFIX, v, vtype)
	g.writeln(buf)

	log.Printf("[genStoreOp] op:0x%x, %s", op, buf)
}

func genMemoryOp(g *CGenContext, op byte) {
	var buf string

	switch op {
	case ops.CurrentMemory:
		_ = g.fetchUint32()
		g.pushStack(g.varn)
		buf = fmt.Sprintf("%s%d.vi32 = vm->pages;", VARIABLE_PREFIX, g.topStack())
	case ops.GrowMemory:
		_ = g.fetchInt8()
		g.pushStack(g.varn)
		ret := g.popStack()

		buf = fmt.Sprintf("%s%d.vi32 = vm->pages; GoGrowMemory(vm, %s%d.vi32);",
			VARIABLE_PREFIX, ret,
			VARIABLE_PREFIX, g.popStack())
		g.pushStack(ret)
	default:
		panic(fmt.Sprintf("[genMemoryOp] invalid op: 0x%x", op))
	}

	g.writeln(buf)
	log.Printf("[genMemoryOp] op:0x%x, %s", op, buf)
}

func genCallGoFunc(g *CGenContext, op byte, index uint32, fsig *wasm.FunctionSig) error {
	buf := bytes.NewBuffer(nil)

	name := g.names[index]
	switch name {
	case "exit":
		g.genGasChecker(op, GasQuickStep)
		buf.WriteString(fmt.Sprintf("GoExit(vm, %s%d.vi32);", VARIABLE_PREFIX, g.popStack()))
	case "abort":
		g.genGasChecker(op, GasQuickStep)
		buf.WriteString("panic(vm, \"Abort\");")
	case "memcpy":
		size := g.popStack()
		src := g.popStack()
		dst := g.popStack()
		g.pushStack(g.varn)
		buf.WriteString(fmt.Sprintf("%s%d.vu32 = TCMemcpy(vm, %s%d.vu32, %s%d.vu32, %s%d.vu32);",
			VARIABLE_PREFIX, g.topStack(),
			VARIABLE_PREFIX, dst,
			VARIABLE_PREFIX, src,
			VARIABLE_PREFIX, size))
	case "memset":
		size := g.popStack()
		c := g.popStack()
		src := g.popStack()
		g.pushStack(g.varn)
		buf.WriteString(fmt.Sprintf("%s%d.vu32 = TCMemset(vm, %s%d.vu32, %s%d.vi32, %s%d.vu32);",
			VARIABLE_PREFIX, g.topStack(),
			VARIABLE_PREFIX, src,
			VARIABLE_PREFIX, c,
			VARIABLE_PREFIX, size))
	case "memmove":
		n := g.popStack()
		src := g.popStack()
		dst := g.popStack()
		g.pushStack(g.varn)
		buf.WriteString(fmt.Sprintf("%s%d.vi32 = TCMemmove(vm, %s%d.vu32, %s%d.vu32, %s%d.vu32);", VARIABLE_PREFIX, g.topStack(),
			VARIABLE_PREFIX, dst, VARIABLE_PREFIX, src, VARIABLE_PREFIX, n))
	case "memcmp":
		n := g.popStack()
		src := g.popStack()
		dst := g.popStack()
		g.pushStack(g.varn)
		buf.WriteString(fmt.Sprintf("%s%d.vi32 = TCMemcmp(vm, %s%d.vu32, %s%d.vu32, %s%d.vu32);", VARIABLE_PREFIX, g.topStack(),
			VARIABLE_PREFIX, dst, VARIABLE_PREFIX, src, VARIABLE_PREFIX, n))
	case "strcmp":
		s2 := g.popStack()
		s1 := g.popStack()
		g.pushStack(g.varn)
		buf.WriteString(fmt.Sprintf("%s%d.vi32 = TCStrcmp(vm, %s%d.vu32, %s%d.vu32);", VARIABLE_PREFIX, g.topStack(),
			VARIABLE_PREFIX, s1, VARIABLE_PREFIX, s2))
	case "strcpy":
		src := g.popStack()
		dst := g.popStack()
		g.pushStack(g.varn)
		buf.WriteString(fmt.Sprintf("%s%d.vu32 = TCStrcpy(vm, %s%d.vu32, %s%d.vu32);",
			VARIABLE_PREFIX, g.topStack(), VARIABLE_PREFIX, dst, VARIABLE_PREFIX, src))
	case "strlen":
		s := g.popStack()
		g.pushStack(g.varn)
		buf.WriteString(fmt.Sprintf("%s%d.vu32 = TCStrlen(vm, %s%d.vu32);",
			VARIABLE_PREFIX, g.topStack(), VARIABLE_PREFIX, s))
	case "atoi":
		s := g.popStack()
		g.pushStack(g.varn)
		buf.WriteString(fmt.Sprintf("%s%d.vi32 = TCAtoi(vm, %s%d.vu32);",
			VARIABLE_PREFIX, g.topStack(), VARIABLE_PREFIX, s))
	case "atoi64":
		s := g.popStack()
		g.pushStack(g.varn)
		buf.WriteString(fmt.Sprintf("%s%d.vi64 = TCAtoi64(vm, %s%d.vu32);",
			VARIABLE_PREFIX, g.topStack(), VARIABLE_PREFIX, s))
	case "TC_Assert":
		cond := g.popStack()
		buf.WriteString(fmt.Sprintf("TCAssert(vm, %s%d.vi32);", VARIABLE_PREFIX, cond))
	case "TC_Require":
		cond := g.popStack()
		buf.WriteString(fmt.Sprintf("TCAssert(vm, %s%d.vi32);", VARIABLE_PREFIX, cond))
	case "TC_RequireWithMsg":
		msg := g.popStack()
		cond := g.popStack()
		buf.WriteString(fmt.Sprintf("TCAssertWithMsg(vm, %s%d.vi32, %s%d.vu32);",
			VARIABLE_PREFIX, cond, VARIABLE_PREFIX, msg))
	case "TC_Revert":
		cond := g.popStack()
		buf.WriteString(fmt.Sprintf("TCAssert(vm, %s%d.vi32);", VARIABLE_PREFIX, cond))
	case "TC_RevertWithMsg":
		msg := g.popStack()
		cond := g.popStack()
		buf.WriteString(fmt.Sprintf("TCAssertWithMsg(vm, %s%d.vi32, %s%d.vu32);",
			VARIABLE_PREFIX, cond, VARIABLE_PREFIX, msg))
	default:
		args := make([]int, len(fsig.ParamTypes))
		for argIndex := range fsig.ParamTypes {
			args[len(fsig.ParamTypes)-argIndex-1] = g.popStack()
		}

		if len(args) > 0 {
			buf.WriteString(fmt.Sprintf("uint64_t args%d[%d] = {", g.calln, len(args)))
			for argIndex, argType := range fsig.ParamTypes {
				if argIndex > 0 {
					buf.WriteString(", ")
				}

				vtype := ""
				switch argType {
				case wasm.ValueTypeI32:
					vtype = "vu32"
				case wasm.ValueTypeI64:
					vtype = "vu64"
				default:
					panic("invalid params type")
				}
				buf.WriteString(fmt.Sprintf("%s%d.%s", VARIABLE_PREFIX, args[argIndex], vtype))
			}
			buf.WriteString("};")
			g.writeln(buf.String())
			buf.Reset()
		}

		if len(fsig.ReturnTypes) > 0 {
			g.pushStack(g.varn)
			switch fsig.ReturnTypes[0] {
			case wasm.ValueTypeI32:
				buf.WriteString(fmt.Sprintf("%s%d.vu32 = GoFunc(vm, env_func_names[%d]", VARIABLE_PREFIX, g.topStack(), index))
			case wasm.ValueTypeI64:
				buf.WriteString(fmt.Sprintf("%s%d.vu64 = GoFunc(vm, env_func_names[%d]", VARIABLE_PREFIX, g.topStack(), index))
			}
		} else {
			buf.WriteString(fmt.Sprintf("GoFunc(vm, env_func_names[%d]", index))
		}

		if len(args) > 0 {
			buf.WriteString(fmt.Sprintf(", %d, &args%d[0]", len(args), g.calln))
			g.calln++
		} else {
			buf.WriteString(fmt.Sprintf(", %d, NULL", len(args)))
		}
		buf.WriteString(");")
	}

	g.writeln(buf.String())
	log.Printf("[genCallGoFunc] op:0x%x, %s", op, buf.String())
	return nil
}

func genCallOp(g *CGenContext, op byte) error {
	index := g.fetchUint32()

	module := g.vm.module
	tIndex := module.Function.Types[index]
	fsig := module.Types.Entries[tIndex]

	if g.lenStack() < len(fsig.ParamTypes) {
		log.Printf("no enough var at stack: params:%d, stack_len:%d", len(fsig.ParamTypes), g.lenStack())
		return fmt.Errorf("[genCallOp] no enough variable at stack")
	}

	if _, ok := g.vm.funcs[index].(goFunction); ok {
		return genCallGoFunc(g, op, index, &fsig)
	}

	args := make([]int, len(fsig.ParamTypes))
	for argIndex := range fsig.ParamTypes {
		args[len(fsig.ParamTypes)-argIndex-1] = g.popStack()
	}

	buf := bytes.NewBuffer(nil)
	if len(fsig.ReturnTypes) > 0 {
		g.pushStack(g.varn)
		switch fsig.ReturnTypes[0] {
		case wasm.ValueTypeI32:
			buf.WriteString(fmt.Sprintf("%s%d.vu32 = %s%d(vm", VARIABLE_PREFIX, g.topStack(), FUNCTION_PREFIX, index))
		case wasm.ValueTypeI64:
			buf.WriteString(fmt.Sprintf("%s%d.vu64 = %s%d(vm", VARIABLE_PREFIX, g.topStack(), FUNCTION_PREFIX, index))
		}
	} else {
		buf.WriteString(fmt.Sprintf("%s%d(vm", FUNCTION_PREFIX, index))
	}

	for argIndex, argType := range fsig.ParamTypes {
		vtype := ""
		switch argType {
		case wasm.ValueTypeI32:
			vtype = "vu32"
		case wasm.ValueTypeI64:
			vtype = "vu64"
		default:
			panic("invalid params type")
		}
		buf.WriteString(fmt.Sprintf(", %s%d.%s", VARIABLE_PREFIX, args[argIndex], vtype))
	}
	buf.WriteString(");")

	g.writeln(buf.String())
	log.Printf("[genCallOp] op:0x%x, %s", op, buf.String())
	return nil
}

func isStackEqual(s1, s2 []int) bool {
	if len(s1) != len(s2) {
		return false
	}

	for i, a := range s1 {
		if a != s2[i] {
			return false
		}
	}
	return true
}

func genJmpOp(g *CGenContext, op byte) {
	buf := bytes.NewBuffer(nil)

	hasStack := func(opStr string, pc int, target uint64) bool {
		oldStack := g.labelStacks[int(target)]
		if len(oldStack) > 0 {
			if !isStackEqual(oldStack, g.stack) {
				panic(fmt.Sprintf("[genJumpOp]%s label already has stack: pc:%d, target:%d", opStr, pc, target))
			}
			return true
		}
		return false
	}

	switch op {
	case compile.OpJmp:
		target := g.fetchUint64()
		if label, ok := g.labelTables[int(target)]; ok {
			buf.WriteString(fmt.Sprintf("goto %s%d;", LABEL_PREFIX, label.Index))

			if hasStack("OpJmp", g.pc, target) {
				break
			}

			log.Printf("[genJumpOp]OpJmp save stack: pc:%d, target:%d, stack[%d]:%v", g.pc, target, g.lenStack(), g.stack)
			newStack := make([]int, g.lenStack())
			copy(newStack, g.stack[0:g.lenStack()])
			g.labelStacks[int(target)] = newStack
		} else {
			log.Printf("[genJumpOp]OpJmp fail: can not find label")
			panic("")
		}
	case compile.OpJmpZ:
		target := g.fetchUint64()
		cond := g.popStack()
		if label, ok := g.labelTables[int(target)]; ok {
			buf.WriteString(fmt.Sprintf("if (likely(%s%d.vu32 == 0)) {goto %s%d;}", VARIABLE_PREFIX, cond,
				LABEL_PREFIX, label.Index))

			if hasStack("OpJmpZ", g.pc, target) {
				break
			}

			log.Printf("[genJumpOp]OpJmpZ save stack: pc:%d, target:%d, stack[%d]:%v", g.pc, target, g.lenStack(), g.stack)
			newStack := make([]int, g.lenStack())
			copy(newStack, g.stack[0:g.lenStack()])
			g.labelStacks[int(target)] = newStack
		} else {
			log.Printf("[genJumpOp]OpJmpZ fail: can not find label")
			panic("")
		}

	case compile.OpJmpNz:
		target := g.fetchUint64()
		preserveTop := g.fetchBool()
		discard := g.fetchInt64()
		cond := g.popStack()
		if label, ok := g.labelTables[int(target)]; ok {
			buf.WriteString(fmt.Sprintf("if (likely(%s%d.vu32 != 0)) {goto %s%d;}", VARIABLE_PREFIX, cond,
				LABEL_PREFIX, label.Index))

			if hasStack("OpJmpNz", g.pc, target) {
				break
			}

			newStack := make([]int, g.lenStack())
			copy(newStack, g.stack[0:g.lenStack()])

			var top int
			if preserveTop {
				top = newStack[len(newStack)-1]
			}
			newStack = newStack[:len(newStack)-int(discard)]
			if preserveTop {
				newStack = append(newStack, top)
			}

			g.labelStacks[int(target)] = newStack
			log.Printf("[genJumpOp]OpJmpNz save stack: pc:%d, target:%d, preserveTop:%v, discard:%d, g.stack:%d, stack[%d]:%v",
				g.pc, target, preserveTop, discard, g.lenStack(), len(newStack), newStack)
		} else {
			log.Printf("[genJumpOp]OpJmpNz fail: can not find label")
			panic("")
		}
	case ops.BrTable:
		index := g.fetchInt64()
		label := g.popStack()
		table := g.branchTables[index]

		buf.WriteString(fmt.Sprintf("switch(%s%d.vu32) {", VARIABLE_PREFIX, label))
		for i, target := range table.Targets {
			if target.Return {
				if !g.f.returns {
					buf.WriteString(fmt.Sprintf("case %d: return 0; ", i))
				} else {
					buf.WriteString(fmt.Sprintf("case %d: return %s%d.vu64; ", i, VARIABLE_PREFIX, g.popStack()))
				}
			} else {
				if label, ok := g.labelTables[int(target.Addr)]; ok {
					buf.WriteString(fmt.Sprintf("case %d: goto %s%d; ", i, LABEL_PREFIX, label.Index))

					if hasStack("BrTabel", g.pc, uint64(target.Addr)) {
						continue
					}

					newStack := make([]int, g.lenStack())
					copy(newStack, g.stack[0:g.lenStack()])

					var top int
					if target.PreserveTop {
						top = newStack[len(newStack)-1]
					}
					newStack = newStack[:len(newStack)-int(target.Discard)]
					if target.PreserveTop {
						newStack = append(newStack, top)
					}

					g.labelStacks[int(target.Addr)] = newStack
					log.Printf("[genJumpOp]BrTable save stack: pc:%d, i:%d, target:%d, preserveTop:%v, discard:%d, g.stack=%d, stack[%d]:%v",
						g.pc, i, target.Addr, target.PreserveTop, target.Discard, g.lenStack(), len(newStack), newStack)
				} else {
					log.Printf("[genJumpOp]BrTable fail: can not find label, i=%d", i)
					panic("")
				}
			}
		}

		target := table.DefaultTarget
		if target.Return {
			if !g.f.returns {
				buf.WriteString("default: return 0; }")
			} else {
				buf.WriteString(fmt.Sprintf("default: return %s%d.vu64; }", VARIABLE_PREFIX, g.popStack()))
			}
		} else {
			if label, ok := g.labelTables[int(target.Addr)]; ok {
				buf.WriteString(fmt.Sprintf("default: goto %s%d; }", LABEL_PREFIX, label.Index))

				if hasStack("BrTable", g.pc, uint64(target.Addr)) {
					break
				}

				newStack := make([]int, g.lenStack())
				copy(newStack, g.stack[0:g.lenStack()])

				var top int
				if target.PreserveTop {
					top = newStack[len(newStack)-1]
				}
				newStack = newStack[:len(newStack)-int(target.Discard)]
				if target.PreserveTop {
					newStack = append(newStack, top)
				}

				g.labelStacks[int(target.Addr)] = newStack
				log.Printf("[genJumpOp]BrTable save stack: pc:%d, target:%d, i:default, preserveTop:%v, discard:%d, g.stack=%d, stack[%d]:%v",
					g.pc, target.Addr, target.PreserveTop, target.Discard, g.lenStack(), len(newStack), newStack)
			} else {
				log.Printf("[genJumpOp]BrTable fail: can not find lable for DefaultTarget")
				panic("")
			}
		}

	default:
		panic(fmt.Sprintf("[genJumpOp] invalid op: 0x%x", op))
	}

	g.writeln(buf.String())
	log.Printf("[genJumpOp] op:0x%x, %s", op, buf.String())
}

func init() {
	log = wasm.NoopLogger{}
}
