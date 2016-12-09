# *A*utomatic *P*rocedure *E*quivalence Tool

APE is a tool for automatically proving the equivalence of programs using modular program verification technology. It showcases an approach to proving the equivalence of programs that differ in the order and amount of dynamic memory allocation. It supports a simple recursive language called *L*. Underlying APE are the tools [Boogie](https://github.com/boogie-org/boogie) and [Z3](https://github.com/Z3Prover/z3).

Details of the tool can be found in [Tim Wood's Phd Thesis (draft pending corrections)](docs/thesis_timwood_20161026.pdf), including a formal proof of the soundness of the methodology.

## Tool Capabilities

The tool was evaluated against a number of micro-testcases and also against several larger examples. In order to illuminate the tool's capabilities we describe here the most important testcases and explain why they are interesting. The [code for the tests cases](src/test/resources) and the [associated generated boogie code](generated-testcases/explicitPermutation) are also available.

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
1. the procedure parameter is reachable from the garbage at the end of v0

&nbsp;
 
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

#### Modular Verification 

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

#### Allocations before a call

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

#### Isomorphism of heap region reachable from call parameters

In order to establish the equivalence of a pair of procedure calls APE attempts to find an isomorphism between the part of the heap reachable from their procedure parameters. In the following example the order of the allocations is reversed between v0 and v1. Note that the result of calling `Callee` is made reachable from the parameter of `Caller`.


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

#### Equivalent calls from non-isomorphic stores

APE can deduce that procedures have equivalent effects even when the pre-stores of the calls are not isomorphic. Instead of checking for isomorphism of the whole store it only checks that the parts of the stores reachable from the call parameters are isomorphic. The following testcases illustrate this. 

##### Allocations may move past calls

Allocations may be moved past calls, provided they are not reachable from the call parameters. In the following example an object is allocated before the call in v0 but after it in v1. Since the allocate memory is not reachable from the call parameter `x` in v0, APE is still able to prove equivalence.

Note that knowledge that the shape of the memory pointed to by `t` in v0 is the same as the shape of the memory pointed to by `t` in v1 persists over the v0 call to `Callee`. This is possible due to the frame axioms automatically used by APE and described in Tim's thesis.

	VERSION 0
	procedure Caller(x) {
	   t := new();
		call Callee(x);
		x.f := t;
	}
	
	procedure Callee(x) {
	   ...
	}
	
	VERSION 1
	procedure Caller(x) {
		call Callee(x);
		t := new();
		x.f := t;
	}
	
	procedure Callee(x) {
	   ...
	}


### Larger Examples  

#### Copying a cyclic data structure

The following examples copies a cyclic data structure. The versions vary in several ways:

1. the nodes of the ring are allocated in the reverse order
1. version 0 allocates an extra garbage element in the base case
1. the sense and order of the conditional is reversed
1. the order of several other instructions differ

The verification time is ~4s

	VERSION 0
	procedure CopyRing(head,r) {
		if(head!=null) {
			head' := new();
			next := head.next;
			call CopyRingUntil(next,head,head',r);
		}
    }

    procedure CopyRingUntil(node,until,head',r) {
		node' := new();
		if(node==until) {
			r.v := head';
		} else {
			next := node.next;
			r' := new();
			call CopyRingUntil(next,until,head',r');
			node'.next := r'.v;
			r.v := node';
		}
	}
	
	VERSION 1
	procedure CopyRing(head,r) {
		if(head!=null) {
			head' := new();
			next := head.next;
			call CopyRingUntil(next,head,head',r);
		}
	}

	procedure CopyRingUntil(node,until,head',r) {
		if(node!=until) {
			r' := new();
			next := node.next;
			call CopyRingUntil(next,until,head',r');
			node' := new();
			r.v := node';
			node'.next := r'.v;
		} else {
			r.v := head';
		}
	}
	
#### Inserting a row into a table

The following example i nserts a key/value pair into a table, replacing any existing occurrence of the key. The versions vary in several ways:

1. In v1 the new row is always allocated at the start, and becomes garbage when the procedure eventually returns. Thus v1 sometimes allocates much more memory than v0.
1. The order of several other instructions differ.
 
Verification time ~31s

	VERSION 0
	procedure Put(table,key,value,r) {
		if(table!=null) {
			if(table.key == key) {
				r.v := table.value;
				table.value := value;
			} else {
				l := new();
				next := table.next;
				call Last(next,l);
				if(l.v != null) {
					table.next := new();
					table.next.key := key;
					table.next.value := value;
				} else {
					call Put(next,key,value,r);
				}
			}
		}
	}

	procedure Last(table,r)
	{
		if(table == null) {
			r.v := new();
		}
	}

	VERSION 1
	procedure Put(table,key,value,r) {
		row := new();
		row.key := key;
		row.value := value;
	
		if(table!=null) {
			next := table.next;
			if(table.key == key) {
				r.v := table.value;
				table.value := value;
			} else {
				l := new();
				call Last(next,l);
				if(l.v != null) {
					table.next := row;
				} else {
					call Put(next,key,value,r);
				}
			}
		}
	}

	procedure Last(table,r)
	{
		if(table == null) {
			r.v := new();
		}
	}