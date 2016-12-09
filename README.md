# *A*utomatic *P*rocedure *E*quivalence Tool

APE is a tool for automatically proving the equivalence of programs using modular program verification technology. It showcases an approach to proving the equivalence of programs that differ in the order and amount of dynamic memory allocation. It supports a simple recursive language called *L*. Underlying APE are the tools [Boogie](https://github.com/boogie-org/boogie) and [Z3](https://github.com/Z3Prover/z3).

Details of the tool can be found in [Tim Wood's Phd Thesis (draft pending corrections)](docs/thesis_timwood_20161026.pdf), including a formal proof of the soundness of the methodology.

## Tool Capabilities

The tool was evaluated against a number of micro-testcases and also against several larger examples. In order to illuminate the tool's capabilities we describe here the most important testcases and explain why they are interesting.

### Changing the order of allocations

In the following test case two objects are allocated and assigned to fields of the procedure parameter. APE ignores garbage so assigning the new objects into fields prevents them from being ignored. In version 0 (v0) the object allocated first is assigned into the field `f` and the second is assigned into the field `g`. In version 1 (v1) the first object allocate is assigned into the field `g` and the second into the field `f`. Despite this change in allocation order, APE proves the procedure are equivalent by proving that the final stores of the procedures are isomorphic modulo garbage for all initial stores. 

	VERSION 0
	procedure DoubleAllocation(x) {
		t := new();
		u := new();
		
		x.f := t;
		x.g := u;
	}
	
	VERSION 1
	procedure DoubleAllocation(x) {
		t := new();
		u := new();
		
		x.g := t;
		x.f := u;
	}
     
### Changing the amount allocated

In the following test case v1 allocates a single object, whereas v2 allocates on objects. APE uses a definition of equivalence that is insensitive to the amount of garbage. APE proves that these procedures always result in isomorphic final stores despite the different numbers of allocations.

	VERSION 0
	procedure SingleGarbageAllocation(x) {
		t := new();
	}
	
	VERSION 1
	procedure SingleGarbageAllocation(x) {
	}
	
In the following test case v0 allocates more memory that v1. APE proves that the procedures are equivalent because the extra memory that v0 allocates is garbage by the end of the procedure. It is interesting to note that:

1. some of the memory that is garbage at the end of the procedure is made reachable during execution of v0  
1. the garbage from v0 has different shape than the garbage from v1
1. the procedure parameter is reachable from the garbage at the end of vv
 
	VERSION 0
	procedure DifferentShapedGarbage(x) {
		t := new();
		u := new();
		t.f := x;
		x.f := x;
		x.g := t;
		x.g := new();
	}
	
	VERSION 1
    procedure DifferentShapedGarbage(x) {
        t := new();
        x.f := x;
        x.g := new();
	}
	
### Procedure Calls

APE is a modular verification tool. It proves the equivalence of pairs of similarly named procedures by assuming that calls to similarly named procedures behave equivalently. If it can verify the equivalence of all such pairs of procedures then the assumptions are justified and the equivalence proof is sound.

The following example shows a pair of procedures that make a single call to another procedure. APE proves that they are equivalent by proving that the versions of `Caller` are equivalent (under the assumption that the versions of `Callee` are equivalent) and then proving that the versions of `Callee` are equivalent.  

	VERSION 0
	procedure Caller(x) {
		call Callee(x);
	}
	
	procedure Callee(x) {
	   ...
	}
	
	VERSION 1
	procedure Caller(x) {
		call Callee(x);
	}
	
	procedure Callee(x) {
	   ...
	}


Allocations may occur before a procedure call. In the following example the order of the allocations differ between v0 and v1.

	VERSION 0
	procedure Caller(x)
	{
	   t := new();
	   u := new();
		call Callee(x);
		x.f := t;
		x.g := u;
	}
	
	procedure Callee(x)
	{
		...
	}
	
	VERSION 1
	procedure Caller(x)
	{
		u := new();
		t := new();
		call Callee(x);
		x.f := t;
		x.g := u;
	}
	
	procedure Callee(x)
	{
		...
	}


In order to establish the equivalence of a pair of procedure calls APE attempts to find an isomorphism between the part of the heap reachable from their procedure parameters. In the following example the order of the allocations is reversed between v0 and v1. Note that:

1. The result of calling `Callee` is made reachable from the parameter of `Caller`.
1. Knowledge that the shape of the memory pointed to by `u` in v0 is the same as the shape of the memory pointed to by `t` in v1 persists over the calls to `Callee`. This is possible due to the frame axioms automatically used by APE and described in Tim's thesis.

	VERSION 0
	procedure Caller(x)
	{
	   t := new();
	   u := new();
		call Callee(x,t);
		x.f := t.v;
		x.g := u;
	}
	
	procedure Callee(x,y)
	{
		
	}
	
	VERSION 1
	procedure Caller(x)
	{
	   t := new();
	   u := new();
		call Callee(x, u);
		x.f := u.v;
		x.g := t;
	}
	
	procedure Callee(x,y)
	{
		
	}
  