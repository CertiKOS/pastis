/* Quentin Carbonneaux - 2016 */
/* Van Chan Ngo, 2016 */

#include <iostream>
#include <fstream>
#include <vector>
#include <set>
#include <algorithm>
#include <functional>
#include <stack>
#include <queue>

#include <llvm/IR/LLVMContext.h>
#include <llvm/Bitcode/ReaderWriter.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Constant.h>
#include <llvm/IR/Constants.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Support/MemoryBuffer.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/STLExtras.h>

using namespace llvm;

class Dumper {
	std::ostream &os;

public:
	void put_byte(uint8_t x)
	{
		os.put(x);
	}

	void put(int64_t x)
	{
		for (int s = 56; s >= 0; s -= 8)
			os.put((uint8_t)(x >> s));
	}

	void put(std::string s)
	{
		put(s.size());
		os << s;
	}

	Dumper(std::ostream &s) : os(s) {}
};

struct Expr {

	/* Expression class to build and output
	 * the expressions used by the compexity
	 * analysis.
	 */

	enum Type {
		Add = 1,
		Sub = 2,
		Mul = 3,
		Num = 4,
		Var = 5,
		Rnd = 6
	};

	Type type;
	int64_t value;
	std::string var;
	std::unique_ptr<Expr> left, right;

	bool isRandom()
	{
		return type == Rnd;
	}

	void iterVars(const std::function<void(std::string &)> &f)
	{
		switch (type) {
		case Add:
		case Sub:
		case Mul:
			left->iterVars(f);
			right->iterVars(f);
			break;
		case Var:
			f(var);
			break;
		case Num:
		case Rnd:
			break;
		}
	}

	void serialize(Dumper &se)
	{
		se.put_byte(type);
		switch (type) {
		case Add:
		case Sub:
		case Mul:
			left->serialize(se);
			right->serialize(se);
			break;
		case Num:
			se.put(value);
			break;
		case Var:
			se.put(var);
			break;
		case Rnd:
			break;
		}
	}

	friend std::ostream &operator<<(std::ostream &os, const Expr &e)
	{
		switch (e.type) {
		case Rnd:
			return os << "random";
		case Var:
			return os << e.var;
		case Num:
			return os << e.value;
		case Add:
			return os << "(" << *e.left << " + " << *e.right << ")";
		case Sub:
			return os << "(" << *e.left << " - " << *e.right << ")";
		case Mul:
			return os << "(" << *e.left << " * " << *e.right << ")";
		}
		return os;
	}

	Expr(Type t, std::unique_ptr<Expr> l, std::unique_ptr<Expr> r)
	: type(t), left(std::move(l)), right(std::move(r))
	{
		if (left->isRandom() || right->isRandom()) {
			type = Rnd;
			left = nullptr;
			right = nullptr;
		}
	}

	Expr(int64_t con)
	: type(Num), value(con) {}

	Expr(std::string v)
	: type(Var), var(v) {}

	Expr()
	: type(Rnd) {}
};

struct Cond {

	/* Conditions matched by the translator are
	 * very simple because C's && and || are
	 * translated to branches.
	 */

	enum Type {
		True   = 1,
		False  = 2,
		Random = 3,
		LE     = 4,
		GE     = 5,
		LT     = 6,
		GT     = 7,
		EQ     = 8,
		NE     = 9,
	};

	Type type;
	std::shared_ptr<Expr> left, right;

	bool isRandomOrTrue()
	{
		return type == Random || type == True;
	}

	Cond negate()
	{
		Type t;
		switch (type) {
		case True:
			t = False;
			break;
		case False:
			t = True;
			break;
		case LE:
			t = GT;
			break;
		case GE:
			t = LT;
			break;
		case LT:
			t = GE;
			break;
		case GT:
			t = LE;
			break;
		case EQ:
			t = NE;
			break;
		case NE:
			t = EQ;
			break;
		case Random:
			t = Random;
			break;
		}
		return Cond(t, left, right);
	}

	void iterVars(const std::function<void(std::string &)> &f)
	{
		switch (type) {
		case True:
		case False:
		case Random:
			break;
		case LE:
		case GE:
		case LT:
		case GT:
		case EQ:
		case NE:
			left->iterVars(f);
			right->iterVars(f);
			break;
		}
	}

	void serialize(Dumper &se)
	{
		se.put_byte(type);
		switch (type) {
		case True:
		case False:
		case Random:
			break;
		case LE:
		case GE:
		case LT:
		case GT:
		case EQ:
		case NE:
			left->serialize(se);
			right->serialize(se);
			break;
		}
	}

	friend std::ostream &operator<<(std::ostream &os, const Cond &c)
	{
		switch(c.type) {
		case True:
			return os << "true";
		case False:
			return os << "false";
		case Random:
			return os << "random";
		case LE:
			return os << *c.left << " <= " << *c.right;
		case GE:
			return os << *c.left << " >= " << *c.right;
		case LT:
			return os << *c.left << " < " << *c.right;
		case GT:
			return os << *c.left << " > " << *c.right;
		case EQ:
			return os << *c.left << " = " << *c.right;
		case NE:
			return os << *c.left << " != " << *c.right;
		}
		return os;
	}

	Cond(Type t, std::shared_ptr<Expr> l, std::shared_ptr<Expr> r)
	: type(t), left(std::move(l)), right(std::move(r))
	{
		if ((left && left->isRandom())
		||  (right && right->isRandom())) {
			type = Random;
			left = nullptr;
			right = nullptr;
		}
	}

	Cond(Type t)
	: type(t) {}

	Cond()
	: type(Random) {}
};

struct Edge {

	/* An edge of the graph we will pass to
	 * the complexity analysis.  Edges bear
	 * program actions on them.
	 */

	enum Type {
		Guard  = 1,
		Assign = 2,
		None   = 3,
		Invalid,
	};

	Type type;
	unsigned dest;
	Cond cond;
	std::string var;
	std::unique_ptr<Expr> expr;

	void iterVars(const std::function<void(std::string &)> &f)
	{
		switch (type) {
		case Guard:
			cond.iterVars(f);
			break;
		case Assign:
			f(var);
			expr->iterVars(f);
			break;
		case None:
		case Invalid:
			break;
		}
	}

	void serialize(Dumper &se)
	{
		se.put_byte(type);
		switch (type) {
		case Guard:
			cond.serialize(se);
			break;
		case Assign:
			se.put(var);
			expr->serialize(se);
			break;
		case None:
			break;
		case Invalid:
			assert(!"reachable");
			break;
		}
		se.put(dest);
	}

	Edge(unsigned d, const Cond &c)
	: type(Guard), dest(d), cond(c)
	{
		if (cond.isRandomOrTrue()) {
			type = None;
			cond = Cond();
		}
	}

	Edge(unsigned d, const std::string &v, std::unique_ptr<Expr> e)
	: type(Assign), dest(d), var(v), expr(std::move(e)) {}

	Edge(unsigned d)
	: type(None), dest(d) {}
};

struct Func {

	std::string name;
	std::vector<std::string> arguments;
	std::vector<std::vector<Edge>> body;
	unsigned start, ret;
	std::set<std::string> unsignedVars;
	unsigned nextNode;

	unsigned newNode()
	{
		return nextNode++;
	}

	void addEdge(unsigned s, Edge &&e)
	{
		assert(s < nextNode && e.dest < nextNode);
		body.resize(nextNode);
		body.at(s).push_back(std::move(e));
	}

	std::vector<Edge>* getEdgesAt(unsigned s)
	{
		return &body.at(s);
	}

	unsigned getNodeSize() {
		return body.size();
	}

	void serialize(Dumper &se)
	{
		std::set<std::string> locals;
		std::sort(arguments.begin(), arguments.end());
		auto collect = [&] (std::string &s) {
			auto low = std::lower_bound(arguments.begin(), arguments.end(), s);
			if (low == arguments.end() || *low != s)
				locals.insert(s);
		};
		for (std::vector<Edge> &ve: body)
			for (Edge &e: ve)
				e.iterVars(collect);
		se.put(name);
		se.put(arguments.size());
		for (std::string &arg: arguments)
			se.put(arg);
		se.put(locals.size());
		for (const std::string &loc: locals)
			se.put(loc);
		se.put(start);
		se.put(ret);
		se.put(body.size());
		for (std::vector<Edge> &ve: body) {
			se.put(ve.size());
			for (Edge &e: ve)
				e.serialize(se);
		}
	}

	Func(const std::string &n, const std::vector<std::string> &args)
	: name(n), arguments(args), ret(-1u), nextNode(0) {}
};

std::string valueName(Value *v)
{
	if (CastInst *CI = dyn_cast<CastInst>(v))
		return valueName(CI->getOperand(0));

	if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(v)) {
#if LLVM_MAJOR > 3 || (LLVM_MAJOR == 3 && LLVM_MINOR >= 8)
		const DataLayout &DL = GEP->getModule()->getDataLayout();
#else
		const DataLayout &DL = *GEP->getDataLayout();
#endif
		APInt Off(64, 0);
		GEP->accumulateConstantOffset(DL, Off);
		Value *vptr = GEP->getPointerOperand();
		return valueName(vptr) + "_off" + Off.toString(10, true);
	}

	if (LoadInst *LI = dyn_cast<LoadInst>(v))
		return valueName(LI->getPointerOperand()) + "_dref";

	if (v->hasName())
		return v->getName();

	for (User *U: v->users())
		if (StoreInst *SI = dyn_cast<StoreInst>(U))
			if (Argument *Arg = dyn_cast<Argument>(SI->getValueOperand()))
				if (Arg->getType()->isPointerTy())
					v->takeName(Arg);

	if (!v->hasName())
		v->setName("_tmp");

	return v->getName();
}

bool checkAllUses(Value *v)
{
	/* Checks that the value is only used in loads
	 * and in at most one store where the stored value
	 * is an argument.
	 */

	int nstore = 0;
	for (User *U: v->users()) {
		if (StoreInst *SI = dyn_cast<StoreInst>(U)) {
			if (!isa<Argument>(SI->getValueOperand()))
				return false;
			nstore++;
		}
		else if (!isa<LoadInst>(U))
			return false;
	}
	return nstore <= 1;
}

bool isTracked(Value *v, bool ptr = false)
{
	/* TODO: Use LLVM's alias analysis to make sure those variables
	   are only modified through GEPs of the same kind.
	*/
	if (CastInst *CI = dyn_cast<CastInst>(v)) {
		return isTracked(CI->getOperand(0), ptr);
	}

	if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(v)) {
		if (!GEP->hasAllConstantIndices())
			return false;
		return !ptr && isTracked(GEP->getPointerOperand(), ptr);
	}

	if (LoadInst *LI = dyn_cast<LoadInst>(v)) {
		return !ptr && isTracked(LI->getPointerOperand(), true);
	}

	if (AllocaInst *AI = dyn_cast<AllocaInst>(v)) {
		if (!AI->isStaticAlloca())
			return false;
		return !ptr || checkAllUses(AI);
	}

	return false;
}

std::unique_ptr<Expr> valueExpr(Value *v)
{
	if (isa<Instruction>(*v)) {

		if (LoadInst *LI = dyn_cast<LoadInst>(v)) {
			Value *vptr = LI->getPointerOperand();
			if (isTracked(vptr))
				return make_unique<Expr>(valueName(vptr));
		}

		if (BinaryOperator *BO = dyn_cast<BinaryOperator>(v)) {
			Expr::Type ety;

			switch (BO->getOpcode()) {
			case Instruction::Add:
				ety = Expr::Add;
				break;
			case Instruction::Sub:
				ety = Expr::Sub;
				break;
			case Instruction::Mul:
				ety = Expr::Mul;
				break;
			default:
				return make_unique<Expr>();
			}

			return make_unique<Expr>(
				ety,
				valueExpr(BO->getOperand(0)),
				valueExpr(BO->getOperand(1))
			);
		}
	}

	if (isa<Argument>(*v))
		return make_unique<Expr>(v->getName());

	if (ConstantInt *CI = dyn_cast<ConstantInt>(v)) {
		int64_t truncVal = CI->getValue().getLimitedValue();
		switch (CI->getType()->getIntegerBitWidth()) {
		case 8:
			return make_unique<Expr>((int8_t)truncVal);
		case 16:
			return make_unique<Expr>((int16_t)truncVal);
		case 32:
			return make_unique<Expr>((int32_t)truncVal);
		default:
			return make_unique<Expr>(truncVal);
		}
	}

	return make_unique<Expr>();
}

Cond valueCond(Value *v, Func &f)
{
	if (ICmpInst *CI = dyn_cast<ICmpInst>(v)) {
		Cond::Type cty;

		switch(CI->getSignedPredicate()) {
		case CmpInst::ICMP_EQ:
			cty = Cond::EQ;
			break;
		case CmpInst::ICMP_NE:
			cty = Cond::NE;
			break;
		case CmpInst::ICMP_SLE:
			cty = Cond::LE;
			break;
		case CmpInst::ICMP_SLT:
			cty = Cond::LT;
			break;
		case CmpInst::ICMP_SGE:
			cty = Cond::GE;
			break;
		case CmpInst::ICMP_SGT:
			cty = Cond::GT;
			break;
		default:
			return Cond();
		}

		auto vl = valueExpr(CI->getOperand(0));
		auto vr = valueExpr(CI->getOperand(1));

		if (CI->isUnsigned()) {
			if (vl->type == Expr::Var)
				f.unsignedVars.insert(vl->var);
			if (vr->type == Expr::Var)
				f.unsignedVars.insert(vr->var);
		}

		return Cond(cty, std::move(vl), std::move(vr));
	}

	if (ConstantInt *CI = dyn_cast<ConstantInt>(v)) {
		if (CI->getValue() == 0)
			return Cond(Cond::False);
		else
			return Cond(Cond::True);
	}

	return Cond();
}

unsigned processBlock(BasicBlock *BB, Func &f, DenseMap<BasicBlock *, unsigned> &bbMap)
{
	unsigned node = -1u;

	{
		auto it = bbMap.find(BB);
		if (it != bbMap.end()) {
			node = it->second;
			if (node == -1u)
				return it->second = f.newNode();
			else
				return node;
		}
	}

	bbMap[BB] = -1u;

	for (auto BI = BB->rbegin(), BE = BB->rend(); BI != BE; ++BI) {
		Instruction *CurI = &*BI;
		if (StoreInst *SI = dyn_cast<StoreInst>(CurI)) {

			/* The only kind of regular instructions
			 * that triggers inspection is stores to
			 * local variables.  When we spot one, we
			 * try to fetch the full expression that
			 * is assigned and export it.
			 */

			Value *vptr = SI->getPointerOperand();
			Value *vop = SI->getValueOperand();
			if (vop->getType()->isIntegerTy() && isTracked(vptr)) {
				unsigned newNode = f.newNode();
				auto e = valueExpr(vop);
				f.addEdge(newNode, {node, valueName(vptr), std::move(e)});
				node = newNode;
			}
		}

		else if (BranchInst *BI = dyn_cast<BranchInst>(CurI)) {
			if (BI->isConditional()) {
				Cond C = valueCond(BI->getCondition(), f);
				Cond NotC = C.negate();

				BasicBlock *BBTrue = BI->getSuccessor(0);
				BasicBlock *BBFalse = BI->getSuccessor(1);

				node = f.newNode();

				f.addEdge(node, {processBlock(BBTrue, f, bbMap), C});
				f.addEdge(node, {processBlock(BBFalse, f, bbMap), NotC});
			}
			else {
				BasicBlock *Succ = BI->getSuccessor(0);
				node = f.newNode();
				f.addEdge(node, processBlock(Succ, f, bbMap));
			}

		}

		else if (isa<ReturnInst>(CurI)) {
		Return:
			node = f.newNode();
			if (f.ret != -1u)
				f.addEdge(node, f.ret);
			else
				f.ret = node;
		}

		else if (TerminatorInst *TI = dyn_cast<TerminatorInst>(CurI)) {

			/* Conservative case:
			 * we do not know what the condition for the
			 * jump is, but we know all the different
			 * possible targets.
			 */

			unsigned nsucc = TI->getNumSuccessors();

			if (nsucc == 0) {
				/* This is a sound handling of this situation
				 * only when a single function is analyzed.
				 * Otherwise, proper program abortion should be
				 * modeled.
				 */
				goto Return;
			}

			node = f.newNode();
			for (unsigned s = 0; s < nsucc; ++s) {
				BasicBlock *succ = TI->getSuccessor(s);
				unsigned nodeSucc = processBlock(succ, f, bbMap);
				f.addEdge(node, nodeSucc);
			}
		}
	}

	assert(node != -1u);
	unsigned newNode = bbMap[BB];
	if (newNode == -1u)
		bbMap[BB] = node;
	else
		f.addEdge(newNode, node);
	return node;
}
/* get edge from n1 to n2 in f
 * using BFS algorithm
 */
Edge* getEdgeBetween(Func &f, unsigned n1, unsigned n2, unsigned &foundnode) {
	if (n1 == n2)
		return nullptr;

	std::queue<unsigned> q;
	q.push(n1);

	while (!q.empty()) {
		unsigned currentnode = q.front();
		q.pop();
		std::vector<Edge> *currentnode_edges = f.getEdgesAt(currentnode);
		for (unsigned k = 0; k < currentnode_edges->size(); k++) {
			unsigned childnode = currentnode_edges->at(k).dest;
			if (childnode == n2) {
				foundnode = currentnode;
				return &(currentnode_edges->at(k));
			}
			q.push(childnode);
		}
	}
}

/* fix ugly PHI node */
void fixPHINode(Function &F, Func &f, DenseMap<BasicBlock *, unsigned> &bbMap) {
	for (inst_iterator instIt = inst_begin(F); instIt != inst_end(F); instIt++) {
		if (!isa<PHINode>(&*instIt))
			continue;
		PHINode *phiNode = dyn_cast<PHINode>(&*instIt);
		for (unsigned i = 0; i < phiNode->getNumIncomingValues(); i ++) {
			if (!isa<ConstantInt>(phiNode->getIncomingValue(i)))
				continue;
			ConstantInt *CI = dyn_cast<ConstantInt>((phiNode->getIncomingValue(i)));
			BasicBlock *phiBlock = phiNode->getParent();
			// get a false incoming block
			if (CI->getValue() == 0) {
				BasicBlock *falseBlock = phiNode->getIncomingBlock(i);
				// next block from false branch - 2sd successor
				for (BasicBlock::iterator iphiBlock = phiBlock->begin(), ephiBlock = phiBlock->end(); iphiBlock != ephiBlock; ++iphiBlock) {
					if (BranchInst *bri = dyn_cast<BranchInst>(&*iphiBlock)) {
						BasicBlock *exitBlock = bri->getSuccessor(1);
						// create a direct edge from falseBlock to exitBlock
						auto it_falseNode = bbMap.find(falseBlock);
						auto it_exitNode = bbMap.find(exitBlock);
						auto it_phiNode = bbMap.find(phiBlock);
						if ((it_falseNode != bbMap.end()) && (it_exitNode != bbMap.end())) {
						  unsigned falseNode = it_falseNode->second;
						  unsigned phiNode = it_phiNode->second;
							unsigned exitNode = it_exitNode->second;
							// get edge from falseNode to phiNode
							unsigned foundnode = -1u;
							Edge* foundedge = getEdgeBetween(f, falseNode, phiNode, foundnode);
							if (foundnode != -1u) {
								//std::cout << "found node " << foundedge->dest << " with edge type " << foundedge->type << std::endl;
								foundedge->dest = exitNode;
							}
						}
					}
				}
			}
			// get a true incoming block
			else {
				BasicBlock *trueBlock = phiNode->getIncomingBlock(i);
				// next block from true branch - 1st successor
				if (BranchInst *bri = dyn_cast<BranchInst>(&*instIt)) {
					BasicBlock *exitBlock = bri->getSuccessor(0);
				}
			}
		}
	}
}

Func extractFunc(Function &F)
{
	std::vector<std::string> args;
	for (Argument &A: F.getArgumentList())
		args.push_back(valueName(&A));
	Func f(valueName(&F), args);
	DenseMap<BasicBlock *, unsigned> bbMap;
	unsigned start = processBlock(&F.getEntryBlock(), f, bbMap);

	/* Add guards for variables that appear in unsigned
	 * comparisons.  This allows to handle the following
	 * idiom:
	 *
	 *     void f(unsigned x) {
	 *             while (x--) {
	 *                 ...
	 *             }
	 *     }
	 */
	auto zero = std::make_shared<Expr>(0);
	for (auto const &var: f.unsignedVars) {
		unsigned node = f.newNode();
		Cond cond(Cond::GE, std::make_shared<Expr>(var), zero);
		f.addEdge(node, {start, cond});
		start = node;
	}
	f.start = start;

	/* fix PHI node */
	fixPHINode(F, f, bbMap);

	return f;
}

cl::opt<std::string> OutputFilename("o",
	cl::desc("Select output file"),
	cl::value_desc("filename"),
	cl::init("-")
);
cl::opt<std::string> Filename(
	cl::Positional, cl::Required,
	cl::desc("<input file>")
);
cl::opt<bool> OutDot("dot",
	cl::desc("Dump extracted program in a Graphviz .dot file")
);

int main(int argc, char *argv[])
{
	LLVMContext Context;
	cl::ParseCommandLineOptions(argc, argv);

	ErrorOr<std::unique_ptr<MemoryBuffer>> MemBufOrErr =
		MemoryBuffer::getFile(Filename);
	if (!MemBufOrErr) {
		errs() << argv[0] << ": could not read input file\n";
		return 1;
	}
	std::unique_ptr<MemoryBuffer> MemBuf = std::move(*MemBufOrErr);

	std::unique_ptr<Module> M;
#if LLVM_MAJOR > 3 || (LLVM_MAJOR == 3 && LLVM_MINOR >= 8)
	ErrorOr<std::unique_ptr<Module>> MOrErr =
		parseBitcodeFile(MemBuf->getMemBufferRef(), Context);
	if (MOrErr)
		M = std::move(*MOrErr);
#elif (LLVM_MAJOR == 3 && LLVM_MINOR >= 6)
	ErrorOr<Module *> MOrErr =
		parseBitcodeFile(MemBuf->getMemBufferRef(), Context);
	M = std::unique_ptr<Module>(MOrErr ? *MOrErr : nullptr);
#else
	ErrorOr<Module *> MOrErr =
		parseBitcodeFile(MemBuf.get(), Context);
	M = std::unique_ptr<Module>(MOrErr ? *MOrErr : nullptr);
#endif
	if (!MOrErr) {
		errs() << argv[0] << ": could not parse input file\n";
		return 1;
	}
	M->materializeAll();

	Module::iterator MI = M->begin();
	for (;; ++MI) {
		if (MI == M->end()) {
			errs() << argv[0] << ": empty module\n";
			return 1;
		}
		if (!MI->isDeclaration())
			break;
	}

	Func f = extractFunc(*MI);

	if (OutDot) {
		std::ofstream ofs;
		ofs.open(Filename + ".dot");

		ofs << "digraph " << f.name << "{\n";
		unsigned n = 0, e = 0;;
		for (auto &vec: f.body) {

			ofs << "n_" << n << " [shape=circle,fontsize=8,label=\"";
			if (n == f.start)
				ofs << "start";
			if (n == f.ret)
				ofs << "end";
			ofs << "\"];\n";

			for (auto &edge: vec) {
				if (edge.type == Edge::None) {
					ofs << "n_" << n << " -> " << "n_" << edge.dest << ";\n";
					continue;
				}
				ofs << "e_" << e << " [shape=box,fontsize=12,label=\"";
				switch (edge.type) {
				case Edge::Guard:
					ofs << "guard " << edge.cond;
					break;
				case Edge::Assign:
					ofs << "assign " << edge.var << " = " << *edge.expr;
					break;
				default:
					break;
				}
				ofs << "\"];\n";
				ofs << "n_" << n << " -> " << "e_" << e << ";\n";
				ofs << "e_" << e << " -> " << "n_" << edge.dest << ";\n";
				e++;
			}

			n++;
		}
		ofs << "}\n";
	}

	if (OutputFilename == "-") {
		Dumper se(std::cout);
		f.serialize(se);
	} else {
		std::ofstream ofs(OutputFilename);
		Dumper se(ofs);
		f.serialize(se);
	}

	return 0;
}
