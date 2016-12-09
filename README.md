# *A*utomatic *P*rocedure *E*quivalence Tool

APE is a tool for automatically proving the equivalence of programs using modular program verification technology. It showcases an approach to proving the equivalence of programs that differ in the order and amount of dynamic memory allocation. It supports a simple recursive language called *L*. Underlying APE are the tools [Boogie](https://github.com/boogie-org/boogie) and [Z3](https://github.com/Z3Prover/z3).

Details of the tool can be found in [Tim Wood's Phd Thesis (draft pending corrections)](thesis/thesis_timwood_20161026_draft.pdf), including a formal proof of the soundness of the methodology. The rest of this document illustrates the capabilities of APE by giving examples, that APE can verify, and commentary on the examples.

Table of Contents
=================

  * [<em>A</em>utomatic <em>P</em>rocedure <em>E</em>quivalence Tool](#automatic-procedure-equivalence-tool)
    * [Test Cases and Examples](#test-cases-and-examples)
      * [Changing the order of allocations](#changing-the-order-of-allocations)
      * [Changing the amount allocated](#changing-the-amount-allocated)
      * [Procedure Calls](#procedure-calls)
        * [Modular Verification](#modular-verification)
        * [Allocations before a call](#allocations-before-a-call)
        * [Isomorphism of heap region reachable from call parameters](#isomorphism-of-heap-region-reachable-from-call-parameters)
        * [Equivalent calls from non\-isomorphic stores](#equivalent-calls-from-non-isomorphic-stores)
          * [Allocations may move past calls](#allocations-may-move-past-calls)
          * [Recursive calls may be reordered](#recursive-calls-may-be-reordered)
      * [Larger Examples](#larger-examples)
        * [Recursively copying a cyclic data structure](#recursively-copying-a-cyclic-data-structure)
        * [Recursively inserting a row into a table](#recursively-inserting-a-row-into-a-table)
        * [Recursively copy a list](#recursively-copy-a-list)
        * [Copy the sides of a tree in different orders](#copy-the-sides-of-a-tree-in-different-orders)
      * [Tabulation of Testcases](#tabulation-of-testcases)        

## Test Cases and Examples

The tool was evaluated against a number of micro-testcases and also against several larger examples. In order to illuminate the tool's capabilities we describe here the *most important* testcases and explain why they are interesting. The [code for all 30+ tests cases](src/test/resources/com/lexicalscope/bl/verification) and the [associated generated boogie code](generated-testcases/explicitPermutation) are also available.

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

In the following test case v1 allocates a single object, whereas v2 allocates no objects. APE uses a definition of equivalence that is insensitive to the amount of garbage. APE proves that these procedures always result in isomorphic final stores despite the different numbers of allocations.

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

##### Recursive calls may be reordered

In the following testcase the order of the recursive calls is reversed. APE uses an encoding of mutual summaries to allow it to search for equivalences between procedure calls, please see [Tim's Phd Thesis](docs/thesis_timwood_20161026.pdf) for further details. This testcase also shows how APE takes advantage of procedure specifications that are available. Here the postcondition annotation `modifies {r}` is present and helps APE to prove that the procedures are equivalent. APE also checks that such annotations are correct.   


	VERSION 0
	procedure Caller(x, r)
  		modifies {r}; 
	{
		if(x != null) {
			r0 := new();
			r1 := new();
				    
		    t0 := x.f;
			call Caller(t0, r0);
					
			t1 := x.g;
			call Caller(t1, r1);
					
			r.f := r0.v;
			r.g := r1.v;
		}
	}
	
	VERSION 1
	procedure Caller(x, r)
	  modifies {r}; 
	{
		if(x != null) {
			r0 := new();
			r1 := new();
				    
		   t0 := x.g;
			call Caller(t0, r0);
					
			t1 := x.f;
			call Caller(t1, r1);
					
			r.g := r0.v;
			r.f := r1.v;
		}
	}

### Larger Examples  

#### Recursively copying a cyclic data structure

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
	
#### Recursively inserting a row into a table

The following testcase inserts a key/value pair into a table, replacing any existing occurrence of the key. The versions vary in several ways:

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


#### Recursively copy a list

The following testcase copies a list. The versions vary in several ways:

1. The order of the allocations is reversed.
1. v1 allocates the new node under different conditions to v0. This causes extra garbage for some executions of v1.
1. An allocation that happens before the recursive call in v1 happens after in v0.
1. The conditions for some instructions and the order of some assignments vary

Verification time ~7s

	VERSION 0
	procedure CopyList(x,y)
	{
	   	if(x!=null) 
		{
			if(y!=null)
			{
			   r := new();
			   xn := x.n;
				call CopyList(xn, r);
				
				t := new();
				// copy head data here
				
				t.n := r.v;
				y.v := t;
			}
		}
	}

	VERSION 1
	procedure CopyList(x,y)
	{
	   	if(x!=null) 
		{
			t := new();
			// copy head data here

		   xn := x.n;
		    
			if(y!=null)
			{
			   r := new();
				call CopyList(xn, r);
				
				y.v := t;
				t.n := r.v;
			}
		}
	}

#### Copy the sides of a tree in different orders

The following testcase recursively copies a tree. The versions vary in several ways:

1. The order of the recursive calls is reversed; v0 copies the left side of the tree first whereas v1 copies the right side first. APE uses an encoding of mutual summaries to allow it to search for equivalences between procedure calls, please see [Tim Wood's Phd Thesis](docs/thesis_timwood_20161026.pdf) for further details. 
1. This testcase also shows how APE takes advantage of procedure specifications that are available. In this case, the postcondition annotation `modifies {r}` is present and helps APE to prove that the procedures are equivalent. APE also checks that such annotations are correct.   

Verification time ~130s

	VERSION 0
	procedure CopyTree(x, r)
	  modifies {r}; 
	{
		if(x!=null) { 
	   		if(r!= null) {
				r0 := new();
			   r1 := new();
			   n := new();
			    
			   t0 := x.f;
				call CopyTree(t0, r0);
				
				t1 := x.g;
				call CopyTree(t1, r1);
				
				n.f := r0.v;
				n.g := r1.v;
				r.v := n;
	  		}
	  	}
	}

	VERSION 1
	procedure CopyTree(x, r)
	  modifies {r}; 
	{
		if(x!=null) { 
			if(r!= null) {
				r0 := new();
				r1 := new();
			    
				t0 := x.g;
				call CopyTree(t0, r1);
				
				t1 := x.f;
				call CopyTree(t1, r0);
				
				n := new();
				n.f := r0.v;
				n.g := r1.v;
				r.v := n;
			}
		}
	}

### Tabulation of Testcases

Here we tabulate the other micro-benchmarks and testcases with a brief explaination of what each one shows

|Description|Reason|Case|
|-----------|------|----|
|Allocation moves past a call|Testing framing of unreachable allocations|[AllocationMovesPastCall.bl](src/test/resources/com/lexicalscope/bl/verification/AllocationMovesPastCall.bl)|
|Allocations passed to call out of order|Testing procedure parameter isomorphism|[AllocationsPassedToCall.bl](src/test/resources/com/lexicalscope/bl/verification/AllocationsPassedToCall.bl)|
|A procedure with a call|Testing modular verification|[Call001.bl](src/test/resources/com/lexicalscope/bl/verification/Call001.bl)|
|A procedure with several calls|Testing modular verification|[Call002.bl](src/test/resources/com/lexicalscope/bl/verification/Call002.bl)|
|A conditional is reversed and some procedures called|Testing solving of conditions|[Conditional001.bl](src/test/resources/com/lexicalscope/bl/verification/Conditional001.bl)|
|Then else branches swapped|Test that non-equivalent conditionals fail to verify|[Conditional002.bl](src/test/resources/com/lexicalscope/bl/verification/Conditional002.bl)|
|Longer example of a cycle|Testing [several features together](#recursively-copying-a-cyclic-data-structure)|[CopyCycle.bl](src/test/resources/com/lexicalscope/bl/verification/CopyCycle.bl)|
|A procedure is called with non-isomorphic parameters|Check that non-isomorphic parameters cause erification failure|[DifferentParameters.bl](src/test/resources/com/lexicalscope/bl/verification/DifferentParameters.bl)|
|More garbage allocations in one version|Test that garbage with a [complex shape is ignored](#changing-the-amount-allocated)|[DifferInShapeOfGarbage.bl](src/test/resources/com/lexicalscope/bl/verification/DifferInShapeOfGarbage.bl)|
|Extra garbage is allocated|Test that garbage is ignored|[DifferInSingleGarbageAllocation.bl](src/test/resources/com/lexicalscope/bl/verification/DifferInSingleGarbageAllocation.bl)|
|Memory allocated in different orders is made reachable|Test that allocation order is ignored|[DoubleAllocationInDifferentOrders.bl](src/test/resources/com/lexicalscope/bl/verification/DoubleAllocationInDifferentOrders.bl)|
|Empty procedures|Test that empty procedures are equivalent|[Empty.bl](src/test/resources/com/lexicalscope/bl/verification/Empty.bl)|
|Allocation and call reordering|Test framing axioms|[Frame001.bl](src/test/resources/com/lexicalscope/bl/verification/Frame001.bl)|
|Memory allocated before a call is made reachable|Test framing axioms|[Frame002.bl](src/test/resources/com/lexicalscope/bl/verification/Frame002.bl)|
|Memory allocated before a call is modified non-isomorphically afterwards|Test that verification fails for non isomorphic memory when frame axioms are active|[Frame003.bl](src/test/resources/com/lexicalscope/bl/verification/Frame003.bl)|
|A procedure modifies something not in its modifies clause|Test that incorrect modifies clauses are detected|[Frame005.bl](src/test/resources/com/lexicalscope/bl/verification/Frame005.bl)|
|Pure procedures are called with non isomorphic parameters|Test that side effect free procedures can be reasoned about|[Frame006.bl](src/test/resources/com/lexicalscope/bl/verification/Frame006.bl)|
|The results of a procedure are ignored|Check that garbage created by a called procedure is ignored|[FramedGarbageOnlyProcedure.bl](src/test/resources/com/lexicalscope/bl/verification/FramedGarbageOnlyProcedure.bl)|
|Side effect free procedures are called|Procedures without side effects are reasoned about|[FramedNoopProcedure.bl](src/test/resources/com/lexicalscope/bl/verification/FramedNoopProcedure.bl)
|Procedures assign different values to fields|non-equivalence is detected||[NonEquiv001.bl](src/test/resources/com/lexicalscope/bl/verification/NonEquiv001.bl)|
|Procedures allocate a list of length 4 and length 5|non-equivalence deeper in the heap is detected|[NonEquiv002.bl](src/test/resources/com/lexicalscope/bl/verification/NonEquiv002.bl)|
|Procedures create a deep heap structure with a difference|non-equivalence deeper in the heap is detected|[NonEquiv003.bl](src/test/resources/com/lexicalscope/bl/verification/NonEquiv003.bl)|
|A tree is copied. One version copies the left side first the other the right side|Tests that a complex data structure and out-of-order procedure calls can be verified together|[ProcedureReturnsValuesViaFramedTemporary.bl](src/test/resources/com/lexicalscope/bl/verification/ProcedureReturnsValuesViaFramedTemporary.bl)|
|Copies a list|Tests that recursive calls with out-of-order allocation and differences in garbage can be verified together|[RecursiveListCopyExample.bl](src/test/resources/com/lexicalscope/bl/verification/RecursiveListCopyExample.bl)|
|Walks a list recursively|Tests that examples with no allocations verify|[RecursivelyWalkList.bl](src/test/resources/com/lexicalscope/bl/verification/RecursivelyWalkList.bl)|
|||[ReorderCalls.bl](src/test/resources/com/lexicalscope/bl/verification/ReorderCalls.bl)|
|||[ReverseAllocationsBeforeCall.bl](src/test/resources/com/lexicalscope/bl/verification/ReverseAllocationsBeforeCall.bl)|
|||[SingleAllocation.bl](src/test/resources/com/lexicalscope/bl/verification/SingleAllocation.bl)|
|||[SingleCall.bl](src/test/resources/com/lexicalscope/bl/verification/SingleCall.bl)|
|||[SingleCallToDifferentProcedures.bl](src/test/resources/com/lexicalscope/bl/verification/SingleCallToDifferentProcedures.bl)|
|||[Swap.bl](src/test/resources/com/lexicalscope/bl/verification/Swap.bl)|
|||[TableInsert.bl](src/test/resources/com/lexicalscope/bl/verification/TableInsert.bl)|
|||[TableInsertNiceNames.bl](src/test/resources/com/lexicalscope/bl/verification/TableInsertNiceNames.bl)|
