/////////////////////////////////////////////////////////////////////////////
// Peano Numbers
type Fuel;
function $Zero():Fuel;
function $Succ(Fuel):Fuel;

/////////////////////////////////////////////////////////////////////////////
// Heap
type Ref;
const $Null : Ref;

type Field alpha;
const unique $Alloc:Field bool;
const unique $E:Field Ref;
const unique $F:Field Ref;
const unique $G:Field Ref;

type Heap = <alpha>[Ref, Field alpha] alpha;

/////////////////////////////////////////////////////////////////////////////
// Well Formed Heap
function $GoodHeap($h:Heap) : bool;
axiom (forall $h:Heap :: $GoodHeap($h) ==> (forall $a:Ref,$f:Field Ref :: !$Allocated($h, $a) ==> $Edge($h,$a,$f, $Null)));
axiom (forall $h:Heap :: $GoodHeap($h) ==> (forall $a:Ref,$f:Field Ref :: $Allocated($h, $a) ==> $Allocated($h, $Read($h,$a,$f))));
axiom (forall $h:Heap :: $GoodHeap($h) ==> $Allocated($h, $Null));
axiom (forall $h:Heap :: $GoodHeap($h) ==> (forall $f:Field Ref :: $Edge($h,$Null,$f, $Null)));

///////////////////////////////////////////////////////////////////
// HeapSuccessor
function $HeapSucc($h,$h':Heap) : bool;
axiom (forall $h:Heap,$a,$a':Ref,$f:Field Ref :: {$GoodHeap($Write($h,$a,$f,$a'))} 
			$GoodHeap($Write($h,$a,$f,$a')) ==> $HeapSucc($h,$Write($h,$a,$f,$a')));
axiom (forall $h:Heap,$a:Ref :: {$GoodHeap($Allocate($h,$a))} 
			$GoodHeap($Allocate($h,$a)) ==> $HeapSucc($h,$Allocate($h,$a)));
// Transitivity of HeapSucc
axiom (forall $h1,$h2,$h3:Heap :: {$HeapSucc($h1,$h2), $HeapSucc($h2,$h3)} 
			$HeapSucc($h1,$h2) && $HeapSucc($h2,$h3) ==> $HeapSucc($h1,$h3));
// Reflexivity of HeapSucc
axiom (forall $h:Heap :: {$GoodHeap($h)} $HeapSucc($h,$h));
			

// allocated this stay allocated
axiom (forall $h,$h':Heap, $a:Ref :: {$HeapSucc($h,$h'), $Allocated($h,$a)}
			$HeapSucc($h,$h') && $Allocated($h,$a) ==> $Allocated($h',$a));

/* is this useful
axiom (forall $h,$h',$h'':Heap, $a:Ref :: {$HeapSucc($h,$h'), $HeapSucc($h,$h''), $Allocated($h',$a)}
			$HeapSucc($h,$h') && 
			$HeapSucc($h,$h'') && 
			$Allocated($h,$a) 
			==> 
			$Allocated($h',$a) && 
			$Allocated($h'',$a));
*/

/////////////////////////////////////////////////////////////////////////////
// Heap Manipulation Functions			
function {:inline true} $Read<alpha>($h:Heap, $a:Ref, $f:Field alpha) : alpha {$h[$a,$f]}
function {:inline true} $Write<alpha>($h:Heap, $a:Ref, $f:Field alpha, $v:alpha) : Heap {$h[$a,$f := $v]}
function {:inline true} $Edge($h:Heap, $a1:Ref, $f:Field Ref, $a2:Ref) : bool {$Read($h,$a1,$f)==$a2}
function {:inline true} $Neighbour($h:Heap, $a1:Ref, $a2:Ref) : bool {(exists $f:Field Ref :: $Edge($h,$a1,$f,$a2))}
function {:inline true} $Allocated($h:Heap, $a:Ref) : bool {$Read($h, $a, $Alloc)}
function {:inline true} $Allocate($h:Heap, $a:Ref) : Heap {$Write($h,$a,$Alloc,true)}
function {:inline true} $New($h:Heap, $h':Heap, $a:Ref) : bool {!$Allocated($h,$a) && $Allocated($h',$a)}

/////////////////////////////////////////////////////////////////////////////
// Roots
type Roots;
function $GoodRoots(roots:Roots) : bool;
function $Root(roots:Roots, a:Ref) : bool;

/////////////////////////////////////////////////////////////////////////////
// Reachable
function $Reachable($h:Heap, $roots:Roots, $x1, $a:Ref) : bool
{
	($a == $x1) ||
	($Root($roots, $a)) || 
	(exists $a':Ref, $f:Field Ref ::
		$Reachable($h, $roots, $x1, $a') &&
   		$Edge($h, $a', $f, $a)
   	)
}

function $SameDiff($h, $heapA, $heapB:Heap, $roots:Roots, $x1, $y1) : bool
{
   true	
}


/////////////////////////////////////////////////////////////////////////////
// Morphism
function $Morphism($heapA, $heapB:Heap, $roots:Roots, $x1, $y1, $a, $b:Ref) : bool
{
	($a == $x1 && $b == $y1) ||
	($a == $b && $Root($roots, $a)) || 
	(exists $a',$b':Ref, $f:Field Ref ::
		$Morphism($heapA, $heapB, $roots, $x1, $y1, $a', $b') &&
   		$Edge($heapA, $a', $f, $a) &&
   		$Edge($heapB, $b', $f, $b)
   	)
}

axiom (forall $heapA, $heapB:Heap, $roots:Roots, $x1, $y1, $a, $b:Ref ::
			$Morphism($heapA, $heapB, $roots, $x1, $y1, $a, $b) ==>
				$Reachable($heapA, $roots, $x1, $a) &&
				$Reachable($heapB, $roots, $y1, $b));

/////////////////////////////////////////////////////////////////////////////
// Isomorphism
function $Isomorphism($heapA, $heapB:Heap, $roots:Roots, $x1, $y1:Ref) : bool
{
	(forall $a,$b,$c :Ref :: 
		{$Allocated($heapA, $a), $Allocated($heapB, $b), $Allocated($heapB, $c)}
		$Morphism($heapA, $heapB, $roots, $x1, $y1, $a, $b) &&
		$Morphism($heapA, $heapB, $roots, $x1, $y1, $a, $c) ==>
		($b == $c)) &&
	(forall $a,$b,$c :Ref :: 
		{$Allocated($heapA, $a), $Allocated($heapA, $b), $Allocated($heapB, $c)}
		$Morphism($heapA, $heapB, $roots, $x1, $y1, $a, $c) &&
		$Morphism($heapA, $heapB, $roots, $x1, $y1, $b, $c) ==>
		($a == $b)) &&
	(forall $a,$b :Ref :: 
		{$Allocated($heapA, $a), $Allocated($heapB, $b)}
		$Morphism($heapA, $heapB, $roots, $x1, $y1, $a, $b) ==>
		(($a == $Null) <==> ($b == $Null)))	
}

/* Is this useful?
axiom (forall $heapA, $heapB:Heap, $roots:Roots, $x1, $y1:Ref :: 
			$Isomorphism($heapA, $heapB, $roots, $x1, $y1) <==> $Isomorphism($heapB, $heapA, $roots, $y1, $x1));
*/

// equal heaps are isomorphic
axiom (forall $heap:Heap, $roots:Roots, $x1:Ref :: 
			(forall $a:Ref :: $Root($roots, $a) ==> $Allocated($heap, $a)) && 
			$Allocated($heap, $x1) 
		==> 
			$Isomorphism($heap, $heap, $roots, $x1, $x1));
	

///////////////////////////////////////////////////////
var $h_1:Heap where $GoodHeap($h_1);
var $h_2:Heap where $GoodHeap($h_2);

///////////////////////////////////////////////////////
procedure $NopPreservesIdentityIso($roots:Roots, x:Ref)
	modifies $h_1,$h_2;
	requires $h_1==$h_2;
	requires $Isomorphism($h_1, $h_2, $roots, x, x);	
	requires $Allocated($h_1, x);
	requires $GoodRoots($roots);
	requires $GoodHeap($h_1);
	//requires $Read($h_1, x, $F) == $Read($h_1, x, $G);
	requires (forall a:Ref :: $Allocated($h_1, a) == $Root($roots, a));
	//requires (forall a:Ref :: (a==x) <==> $Root($roots, a));
	//ensures $Isomorphism(0,0,$h_1,$h_2,x,x);  
{ 
   var tE_1,tF_1,tG_1,tE_2,tF_2,tG_2 : Ref;
   var $h_pre,$h_pre_1, $h_pre_2 : Heap;
   
   $h_pre  := $h_1;
   
   tE_1 := $Read($h_1, x, $E); assert($Allocated($h_1, tE_1));
   tF_1 := $Read($h_1, x, $F); assert($Allocated($h_1, tF_1));
   tG_1 := $Read($h_1, x, $G); assert($Allocated($h_1, tG_1));
   $h_1 := $Write($h_1, x, $E, tG_1); assume $GoodHeap($h_1);
   $h_1 := $Write($h_1, x, $F, tE_1); assume $GoodHeap($h_1);
   $h_1 := $Write($h_1, x, $G, tF_1); assume $GoodHeap($h_1);
   
	//////////////////

   tE_2 := $Read($h_2, x, $E); assert($Allocated($h_2, tE_2));
   tF_2 := $Read($h_2, x, $F); assert($Allocated($h_2, tF_2));
   tG_2 := $Read($h_2, x, $G); assert($Allocated($h_2, tG_2));
   $h_2 := $Write($h_2, x, $G, tF_2); assume $GoodHeap($h_2);
   $h_2 := $Write($h_2, x, $F, tE_2); assume $GoodHeap($h_2);
   $h_2 := $Write($h_2, x, $E, tG_2); assume $GoodHeap($h_2);
   
   assert $Isomorphism($h_1, $h_2, $roots, x, x);
}
