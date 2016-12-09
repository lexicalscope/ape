# *A*utomatic *P*rocedure *E*quivalence Tool

APE is a tool for automatically proving the equivalence of programs. It showcases an approach to proving the equivalence of programs that differ in the order and amount of dynamic memory allocation. It supports a simple recursive language called *L*.

Details of the tool can be found in [Tim Wood's Phd Thesis (draft pending corrections)](docs/thesis_timwood_20161026.pdf), including a formal proof of the soundness of the methodology.

## Tool Capabilities

The tool was evaluated against a number of micro-testcases and also against several larger examples. In order to illuminate the tool's capabilities we describe here the most important testcases and explain why they are interesting.

### Changing the order of allocations

In this test case two objects are allocated and assigned to fields of the procedure parameter. APE ignores garbage so assigning the new objects into fields prevents them from being ignored. In version 0 (v0) the object allocated first is assigned into the field `f` and the second is assigned into the field `g`. In version 1 (v1) the first object allocate is assigned into the field `g` and the second into the field `f`. Despite this change in allocation order, APE proves the procedure are equivalent by proving that the final stores of the procedures are isomorphic modulo garbage for all initial stores. 

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
     