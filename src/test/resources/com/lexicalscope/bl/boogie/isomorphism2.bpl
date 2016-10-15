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
// Morphism
/*
axiom (forall $heapA, $heapB:Heap, $x1, $y1, $a, $b, $a',$b':Ref, $f:Field Ref ::
		$Morphism($heapA, $heapB, $x1, $y1, $a, $b) && 
		$Edge($heapA, $a, $f, $a') &&
   		$Edge($heapB, $b, $f, $b')
   	==> 
   		$Morphism($heapA, $heapB, $x1, $y1, $a', $b'));
*/

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

///////////////////////////////////////////////////////////////////
// Isomorphism of Effects
function $Effect($h_pre:Heap, $h_post:Heap, $a:Ref, $f:Field Ref, $a':Ref) : bool {
	$Read($h_pre,$a,$f)!=$Read($h_post,$a,$f) && $Edge($h_post,$a,$f,$a')
}

function $IsomorphicEffects(
			$p,$q:int,
			$h_pre_1:Heap, $x_1:Ref, $h_post_1:Heap,
			$h_pre_2:Heap, $x_2:Ref, $h_post_2:Heap) : bool;

axiom (forall $p,$q:int,
			$h_pre_1:Heap, $x_1:Ref, $h_post_1:Heap,
			$h_pre_2:Heap, $x_2:Ref, $h_post_2:Heap,
			$a,$a',$b,$b':Ref, $f:Field Ref, $roots:Roots ::
			{$IsomorphicEffects($p,$q, $h_pre_1,$x_1,$h_post_1, $h_pre_2,$x_2,$h_post_2), 
				$Allocated($h_post_1,$a), $Edge($h_post_1,$a,$f,$a'),
				$Allocated($h_post_2,$b), $Edge($h_post_2,$b,$f,$b'),
				$GoodRoots($roots)}
			$IsomorphicEffects($p,$q, $h_pre_1,$x_1,$h_post_1, $h_pre_2,$x_2,$h_post_2) &&
			$Morphism($h_pre_1, $h_pre_2, $roots, $x_1, $x_2, $a, $b)
			==>
			$Morphism($h_post_1, $h_post_2, $roots, $x_1, $x_2, $a, $b)
		);

/*
axiom (forall $p,$q:int,
			$h_pre_1:Heap, $x_1:Ref, $h_post_1:Heap,
			$h_pre_2:Heap, $x_2:Ref, $h_post_2:Heap,
			$a,$a',$b,$b':Ref, $f:Field Ref ::
			$IsomorphicEffects($p,$q, $h_pre_1,$x_1,$h_post_1, $h_pre_2,$x_2,$h_post_2) &&
			$Effect($h_pre_1, $h_post_1, $a, $f, $a') &&
			$Effect($h_pre_2, $h_post_2, $b, $f, $b') &&
			$Morphism($h_pre_1, $h_pre_2, $EmptyRoots(), $x_1, $x_2, $a, $b)
			==>
			(
				($New($h_pre_1,$h_post_1, $a') && $New($h_pre_2,$h_post_2, $b'))
				||
				$Morphism($h_pre_1, $h_pre_2, $EmptyRoots(), $x_1, $x_2, $a', $b')
			)
		);
*/	

//axiom (forall $heapA, $heapB:Heap, $x1, $y1:Ref :: $Isomorphism($heapA, $heapB, $x1, $y1) <==> $Isomorphism($heapB, $heapA, $y1, $x1));

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
	requires $Allocated($h_1, x);
	requires $GoodRoots($roots);
	//requires $Read($h_1, x, $F) == $Read($h_1, x, $G);
	requires (forall a:Ref :: $Allocated($h_1, a) == $Root($roots, a));
	//requires (forall a:Ref :: (a==x) <==> $Root($roots, a));
	//ensures $Isomorphism(0,0,$h_1,$h_2,x,x);  
{ 
   var t1_1,t2_1,t1_2,t2_2 : Ref;
   var $h_pre_1, $h_pre_2 : Heap;
   
   t1_1 := $Read($h_1, x, $F);
   t2_1 := $Read($h_1, x, $G);
   $h_1 := $Write($h_1, x, $G, t1_1); assume $GoodHeap($h_1);
   $h_1 := $Write($h_1, x, $F, t2_1); assume $GoodHeap($h_1);
   
   $h_pre_1 := $h_1;
   call Other_1(0,$roots, x);
   
   //t1_1 := $Read($h_1, x, $F);
   //t2_1 := $Read($h_1, x, $G);
   //$h_1 := $Write($h_1, x, $G, t1_1); assume $GoodHeap($h_1);
   //$h_1 := $Write($h_1, x, $F, t2_1); assume $GoodHeap($h_1);

	//////////////////

   t1_2 := $Read($h_2, x, $F);
   t2_2 := $Read($h_2, x, $G);
   $h_2 := $Write($h_2, x, $G, t1_2); assume $GoodHeap($h_2);
   $h_2 := $Write($h_2, x, $F, t2_2); assume $GoodHeap($h_2);
   
   $h_pre_2 := $h_2;
   call Other_2(1,$roots, x);
   
   //t1_2 := $Read($h_2, x, $F);
   //t2_2 := $Read($h_2, x, $G);
   //$h_2 := $Write($h_2, x, $G, t1_2); assume $GoodHeap($h_2);
   //$h_2 := $Write($h_2, x, $F, t2_2); assume $GoodHeap($h_2);
   
   //assert Other_succ($h_pre_1,$roots,x,$h_1);
   //assert Other_succ($h_pre_2,$roots,x,$h_2);
   //assert $EstablishedIso(0, 1, $roots, $h_pre_1, x, $h_1, $h_pre_2, x, $h_2);

   assert $IsomorphicEffects(0, 1, $h_pre_1, x, $h_1, $h_pre_2, x, $h_2);

   assert $Isomorphism($h_1, $h_2, $roots, x, x);
}

function Other_succ($p:int,$h_pre:Heap,$roots:Roots,$x:Ref,$h_post:Heap) : bool;
function $EstablishedIso(
				$p,$q:int,
	//			$roots:Roots,
				$h_pre_1:Heap,$x_1:Ref,$h_post_1:Heap,
				$h_pre_2:Heap,$x_2:Ref,$h_post_2:Heap) : bool;

function $EmptyRoots() : Roots;
axiom (forall $roots:Roots :: $roots == $EmptyRoots() ==> (forall $a:Ref :: !$Root($roots, $a)));
				
axiom (forall $p:int,$h_pre_1:Heap, $roots_1:Roots, $x_1:Ref, $h_post_1:Heap,
			  $q:int,$h_pre_2:Heap, $roots_2:Roots, $x_2:Ref, $h_post_2:Heap ::
		{Other_succ($p,$h_pre_1,$roots_1,$x_1,$h_post_1), Other_succ($q,$h_pre_2,$roots_2,$x_2,$h_post_2)} 
		Other_succ($p,$h_pre_1,$roots_1,$x_1,$h_post_1) &&
		Other_succ($q,$h_pre_2,$roots_2,$x_2,$h_post_2) &&
		//($roots_1 == $roots_2) &&
		//$Isomorphism($h_pre_1, $h_pre_2, $roots_1, $x_1, $x_2) 
		$Isomorphism($h_pre_1, $h_pre_2, $EmptyRoots(), $x_1, $x_2)
	==>
		$EstablishedIso(
		    $p,$q,
//		 	$roots_1,
		 	$h_pre_1, $x_1, $h_post_1,
		 	$h_pre_2, $x_2, $h_post_2
		));

axiom (forall $p,$q:int,//$roots:Roots, 
		 	  $h_pre_1:Heap, $x_1:Ref, $h_post_1:Heap,
			  $h_pre_2:Heap, $x_2:Ref, $h_post_2:Heap ::
		  $EstablishedIso(
		    $p,$q,
		 	//$roots,
		 	$h_pre_1, $x_1, $h_post_1,
		 	$h_pre_2, $x_2, $h_post_2)
		 ==>
		 //  (forall $roots:Roots :: $Isomorphism($h_post_1, $h_post_2, $roots, $x_1, $x_2)));
	 	   $IsomorphicEffects(
	 	    $p,$q,
			$h_pre_1, $x_1, $h_post_1,
		 	$h_pre_2, $x_2, $h_post_2));


procedure Other_1($p:int,$roots:Roots, x:Ref);
 	modifies $h_1;
	requires $Allocated($h_1,x);
	free ensures (forall a:Ref :: $Allocated(old($h_1),a) ==> $Allocated($h_1,a));
	free ensures $GoodHeap($h_1);
	free ensures Other_succ($p,old($h_1),$roots,x,$h_1);
 
procedure Other_2($p:int,$roots:Roots, x:Ref);
 	modifies $h_2;
	requires $Allocated($h_2,x);
	free ensures (forall a:Ref :: $Allocated(old($h_2),a) ==> $Allocated($h_2,a));
	free ensures $GoodHeap($h_2);
	free ensures Other_succ($p,old($h_2),$roots,x,$h_2);