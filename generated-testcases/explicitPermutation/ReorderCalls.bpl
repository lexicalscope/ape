/////////////////////////////////////////////////////////////////////////////
// Heap
type Ref;
const $Null : Ref;
function $NullObject($a:Ref):bool;
axiom $NullObject($Null);

type Field alpha;
const unique $Alloc:Field bool;
const unique $field#e:Field Ref;
const unique $field#f:Field Ref;
const unique $field#g:Field Ref;
const unique $field#n:Field Ref;
const unique $field#v:Field Ref;
const unique $field#l:Field Ref;
const unique $field#r:Field Ref;
axiom (forall <alpha> $f:Field alpha :: 
	$f==$field#e || 
	$f==$field#f || 
	$f==$field#g || 
	$f==$field#n || 
	$f==$field#v || 
	$f==$field#l || 
	$f==$field#r || 
	$f==$Alloc);

function $Field($f:Field Ref):bool;
axiom 
    $Field($field#e) &&
	$Field($field#e) && 
	$Field($field#f) && 
	$Field($field#g) &&
	$Field($field#n) &&
	$Field($field#v) &&
	$Field($field#l) &&
	$Field($field#r);

type Heap = <alpha>[Ref, Field alpha] alpha;

/////////////////////////////////////////////////////////////////////////////
// Well Formed Heap
function $GoodHeap($h:Heap) : bool;
axiom (forall $h:Heap :: $GoodHeap($h) ==> (forall $a:Ref,$f:Field Ref :: !$Allocated($h, $a) ==> $Edge($h,$a,$f, $Null)));
axiom (forall $h:Heap :: $GoodHeap($h) ==> (forall $a:Ref,$f:Field Ref :: $Allocated($h, $a) ==> $Allocated($h, $Read($h,$a,$f))));
axiom (forall $h:Heap :: $GoodHeap($h) ==> $Allocated($h, $Null));
axiom (forall $h:Heap :: $GoodHeap($h) ==> (forall $f:Field Ref :: $Edge($h,$Null,$f, $Null)));
//axiom (forall $h:Heap :: $GoodHeap($h) ==> (exists $a:Ref :: !$Allocated($h, $a))); // always a free address - is this needed?

///////////////////////////////////////////////////////////////////
// HeapSuccessor
function $HeapSucc($h,$h':Heap) : bool;
axiom (forall $h:Heap,$a,$a':Ref,$f:Field Ref :: {$GoodHeap($h), $GoodHeap($Write($h,$a,$f,$a'))} 
			$GoodHeap($Write($h,$a,$f,$a')) ==> $HeapSucc($h,$Write($h,$a,$f,$a')));
axiom (forall $h:Heap,$a:Ref :: {$GoodHeap($h), $GoodHeap($Allocate($h,$a))} 
			$GoodHeap($Allocate($h,$a)) ==> $HeapSucc($h,$Allocate($h,$a)));
// Transitivity of HeapSucc
axiom (forall $h1,$h2,$h3:Heap :: {$HeapSucc($h1,$h2), $HeapSucc($h2,$h3)} 
			$HeapSucc($h1,$h2) && $HeapSucc($h2,$h3) ==> $HeapSucc($h1,$h3));
// Reflexivity of HeapSucc
//axiom (forall $h:Heap :: {$GoodHeap($h)} $HeapSucc($h,$h));

// allocated stay allocated
axiom (forall $h,$h':Heap, $a:Ref :: {$HeapSucc($h,$h'), $Allocated($h',$a)}
			$HeapSucc($h,$h') && $Allocated($h,$a) ==> $Allocated($h',$a));

////////////////////////////////////////////////////////////////////
// We track objects that have been modified, so we can trigger the
// reachability axioms			
function $Written($h:Heap,$a:Ref) : bool;

axiom (forall $h:Heap,$a,$a':Ref,$f:Field Ref :: {$GoodHeap($Write($h,$a,$f,$a'))} 
			$GoodHeap($Write($h,$a,$f,$a')) ==> $Written($h,$a));

// written stay written
axiom (forall $h,$h':Heap, $a:Ref :: {$HeapSucc($h,$h'), $Written($h,$a)}
          $HeapSucc($h,$h') && $Written($h,$a) ==> $Written($h',$a));

////////////////////////////////////////////////////////////////////
// We track objects that have been read, so we can trigger the
// reachability axioms			
function $ReadObject($h:Heap,$a:Ref) : bool;

// read stay read
axiom (forall $h,$h':Heap, $a:Ref :: {$HeapSucc($h,$h'), $ReadObject($h,$a)}
          $HeapSucc($h,$h') && $ReadObject($h,$a) ==> $ReadObject($h',$a));

////////////////////////////////////////////////////////////////////
// We track objects that have been allocated, so we can trigger the
// reachability axioms	
function $AllocatedObject($h:Heap,$a:Ref) : bool;
// allocated stay allocated
axiom (forall $h,$h':Heap, $a:Ref :: {$HeapSucc($h,$h'), $AllocatedObject($h,$a)}
          $HeapSucc($h,$h') && $AllocatedObject($h,$a) ==> $AllocatedObject($h',$a));

////////////////////////////////////////////////////////////////////
// Interesting Objects are ones that we have read or allocated or written
/*
function $InterestingObject($h:Heap,$a:Ref) : bool;
axiom (forall $h:Heap, $a:Ref :: {$AllocatedObject($h,$a)}
          $AllocatedObject($h,$a) ==> $InterestingObject($h,$a));
axiom (forall $h:Heap, $a:Ref :: {$ReadObject($h,$a)}
          $ReadObject($h,$a) ==> $InterestingObject($h,$a));
axiom (forall $h:Heap, $a:Ref :: {$Written($h,$a)}
          $Written($h,$a) ==> $InterestingObject($h,$a));
axiom (forall $h:Heap :: {$GoodHeap($h)} 
		  $GoodHeap($h) ==> $InterestingObject($h,$Null));
*/  

///////////////////////////////////////////////////////////////////
function $Bigger($h,$h':Heap) : bool
{
   (forall $a:Ref :: $Allocated($h,$a) ==> $Allocated($h',$a))
}

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
function $Root(roots:Roots, a:Ref) : bool;
function $GoodRoots(roots:Roots) : bool;

function $Roots#Allocated($roots:Roots, $h:Heap) : bool
{
    (forall $a:Ref :: 
    	//{$Written($h, $a)} {$ReadObject($h,$a)} {$AllocatedObject($h,$a)}
    	{$Allocated($h, $a)}
    	$Root($roots, $a) ==> $Allocated($h, $a))
}
// roots stay allocated
axiom (forall $h,$h':Heap, $roots:Roots :: {$HeapSucc($h,$h'), $GoodRoots($roots)}
          $HeapSucc($h,$h') && $Roots#Allocated($roots,$h) ==> $Roots#Allocated($roots, $h'));


function $Roots#EverythingAllocatedIsARoot($roots:Roots, $h:Heap) : bool
{
    (forall $a:Ref :: 
    	//{$Written($h, $a)} {$ReadObject($h,$a)} 
    	{$Root($roots, $a)}
    	 $Allocated($h, $a) ==> $Root($roots, $a))
}

function $SameDiff($hpre_1, $hpost_1, $hpre_2, $hpost_2:Heap) : bool
{
	(forall <alpha> $a:Ref,$f:Field alpha :: 
		($Read($hpre_1, $a, $f) != $Read($hpost_1, $a, $f) ==> $Read($hpost_1, $a, $f)==$Read($hpost_2, $a, $f)) &&
		($Read($hpre_2, $a, $f) != $Read($hpost_2, $a, $f) ==> $Read($hpost_1, $a, $f)==$Read($hpost_2, $a, $f)))
}

/////////////////////////////////////////////////////////////////////////////
// Reachability
function $Reachable($h:Heap, $roots:Roots, $a:Ref) : bool
{
   // this trigger improves the performance of list copy example
   (exists $r:Ref :: //{$Written($h, $r)} {$ReadObject($h,$r)} {$Root($roots, $r)} 
   		$Root($roots, $r) && $Reach($h, $r, $a))
}

function $Reach($h:Heap, $a:Ref, $b:Ref) : bool;

axiom (forall $h:Heap :: {$GoodHeap($h)} $GoodHeap($h) ==> $Reach($h, $Null, $Null));
axiom (forall $h:Heap, $a:Ref :: $Allocated($h, $a) ==> $Reach($h, $a, $a));
//axiom (forall $h:Heap, $a,$b:Ref :: $Reach($h, $a, $b) ==> $Allocated($h, $a) && $Allocated($h, $b));
axiom (forall $h:Heap, $a,$b:Ref :: {$Reach($h, $a, $b)} $Reach($h, $a, $b) && $NoInboundEdges($h,$b) ==> $a==$b);
axiom (forall $h:Heap, $a,$b:Ref :: {$GoodHeap($h), $Written($h, $a), $ReadObject($h,$b)}
		$Reach($h,$a,$b) ==> 
			$a == $b ||	(exists $c:Ref,$f:Field Ref :: $Reach($h, $a, $c) && $Edge($h, $c, $f, $b)));
axiom (forall $h:Heap, $a,$b:Ref :: 
			//{$AllocatedObject($h,$a), $NullObject($b)}
			//{$AllocatedObject($h,$a), $Allocated($h, $b)}
			// can't achieve a performance improvement here
		$Reach($h,$a,$b) ==> 
			$a == $b || (exists $c:Ref,$f:Field Ref :: $Edge($h, $a, $f, $c) && $Reach($h, $c, $b)));
//axiom (forall $h:Heap, $a,$b:Ref :: !$Reach($h,$a,$b) ==> (forall $c:Ref :: $Reach($h,$c,$a) ==> !$Reach($h,$c,$b)));
/* existential mid reachability
axiom (forall $h:Heap, $a,$b:Ref :: 
		$Reach($h,$a,$b) && $a != $b ==> 
			  (exists $c,$d:Ref,$f:Field Ref :: $Reach($h, $a, $c) && $Edge($h, $c, $f, $d) && $Reach($h, $d, $b))); */			  		 
//axiom (forall $h:Heap, $a,$b,$c,$d:Ref, $f:Field Ref :: $Reach($h,$a,$b) && $Edge($h, $b, $f, $c) && $Reach($h,$c,$d) ==> $Reach($h,$a,$d));


// everything reachable from the parameters is reachable from a parameter			
//axiom (forall $h:Heap, $x0,$x1:Ref, $a:Ref :: $ReachableFromParams#2($h, $x0, $x1, $a) <==> ($ReachableFromParams#1($h, $x0, $a) || $ReachableFromParams#1($h, $x1, $a)));

// everything reachable from an allocated parameter is allocated
//
// This axiom is important for identifying garbage (infact, I think excluding trying to
// find out if unallocated stuff might be reachable).
axiom (forall $h:Heap, $x0:Ref, $a:Ref :: {$Reach($h, $x0, $a)}
    $GoodHeap($h) && 
	$Reach($h, $x0, $a) &&
	$Allocated($h, $x0) 
	==> $Allocated($h, $a));

// everything reachable from $Null is $Null
axiom (forall $h:Heap, $x0:Ref, $a:Ref ::
    $GoodHeap($h) && 
	$Reach($h, $Null, $a) 
	==> $a == $Null);

// every non null object can reach itself	
//axiom (forall $h:Heap, $a:Ref :: $ReachableFromParams#1($h,$a,$a));    

function $ReachableFromParams#1($h:Heap, $x0:Ref, $a:Ref) : bool
{
   $Reach($h, $x0, $a)
}

// transitivity, is this needed?
//axiom (forall $h:Heap, $a,$b,$c:Ref :: $GoodHeap($h) && $Reach($h,$a,$b) && $Reach($h,$b,$c) ==> $Reach($h,$a,$c)); 


function $FieldsNull($h:Heap, $a:Ref) : bool
{
	(forall $f:Field Ref :: $Edge($h,$a,$f, $Null))
}

function $ReachNull($h:Heap, $a:Ref) : bool
{
	(forall $b:Ref :: $Reach($h,$a,$b) ==> $b==$a || $b==$Null)
}

function $NoInboundEdges($h:Heap, $a:Ref) : bool
{
	(forall $b:Ref, $f:Field Ref :: !$Edge($h,$b,$f,$a))
}

// is this axiom useful? perhaps improves performance
//axiom (forall $h:Heap, $a:Ref :: $GoodHeap($h) && $FieldsNull($h,$a) ==> $ReachNull($h,$a));

function $ReachableFromParams#2($h:Heap, $x0,$x1:Ref, $a:Ref) : bool
{
   $ReachableFromParams#1($h, $x0, $a) || $ReachableFromParams#1($h, $x1, $a)
}

function $ReachableFromParams#4($h:Heap, $x0,$x1,$x2,$x3:Ref, $a:Ref) : bool
{
      $ReachableFromParams#1($h, $x0, $a) 
   || $ReachableFromParams#1($h, $x1, $a)
   || $ReachableFromParams#1($h, $x2, $a)
   || $ReachableFromParams#1($h, $x3, $a)
}

/////////////////////////////////////////////////////////////////////////////
// Extensional Equality
function $Heap#Equal($h_1, $h_2:Heap) : bool
{
   (forall $a:Ref :: 
   		{$Written($h_1,$a)} {$Written($h_2,$a)} 
   			(forall <alpha> $f:Field alpha ::  $Read($h_1, $a, $f) == $Read($h_2, $a, $f)))
}

function $Heap#Bigger($h_0, $h_1:Heap) : bool
{
	(forall $a:Ref :: $Allocated($h_0, $a) ==> $Allocated($h_1, $a))
}

/////////////////////////////////////////////////////////////////////////////
// Reachable Extensional Equality
function $Heap#ReachableEqual($h_1, $h_2:Heap, $roots:Roots) : bool
{
	$Heap#ReachableEqual'($h_1, $h_2, $roots) && $Heap#ReachableEqual'($h_2, $h_1, $roots)
}

function $Heap#ReachableEqual'($h_1, $h_2:Heap, $roots:Roots) : bool
{
	(forall $a:Ref :: {$Written($h_1, $a)} {$Written($h_2, $a)}
		(forall <alpha> $f:Field alpha :: $Reachable($h_1, $roots, $a) ==> $Read($h_1, $a, $f) == $Read($h_2, $a, $f)))
}

function $Heap#EqualFromParams#1($h_0:Heap, $x0_0:Ref, $h_1:Heap, $x0_1:Ref) : bool 
{
	$Heap#EqualFromParams#1'($h_0, $x0_0, $h_1, $x0_1) &&
	$Heap#EqualFromParams#1'($h_1, $x0_1, $h_0, $x0_0)
}

function $Heap#EqualFromParams#1'($h_0:Heap, $x0_0:Ref, $h_1:Heap, $x0_1:Ref) : bool 
{
	$x0_0 == $x0_1 &&
	(forall $a:Ref :: {$Written($h_0,$a)} {$Written($h_1,$a)}
		($Reach($h_0, $x0_0, $a) ==> 
			(forall <alpha> $f:Field alpha :: $Read($h_0, $a, $f) == $Read($h_1, $a, $f))))
}

function $Heap#EqualFromParams#2($h_0:Heap, $x0_0,$x1_0:Ref, $h_1:Heap, $x0_1,$x1_1:Ref) : bool 
{
    $Heap#EqualFromParams#1($h_0, $x0_0, $h_1, $x0_1) &&
    $Heap#EqualFromParams#1($h_0, $x1_0, $h_1, $x1_1)
}

function $Heap#EqualFromParams#4($h_0:Heap, $x0_0,$x1_0,$x2_0,$x3_0:Ref, $h_1:Heap, $x0_1,$x1_1,$x2_1,$x3_1:Ref) : bool 
{
    $Heap#EqualFromParams#1($h_0, $x0_0, $h_1, $x0_1) &&
    $Heap#EqualFromParams#1($h_0, $x1_0, $h_1, $x1_1) &&
    $Heap#EqualFromParams#1($h_0, $x2_0, $h_1, $x2_1) &&
    $Heap#EqualFromParams#1($h_0, $x3_0, $h_1, $x3_1)
}

function $Heap#SameReachableFromParams#4($h_0:Heap, $x0_0,$x1_0,$x2_0,$x3_0:Ref, $h_1:Heap, $x0_1,$x1_1,$x2_1,$x3_1:Ref) : bool
{
	$Heap#SameReachableFromParams#1($h_0, $x0_0, $h_1, $x0_1) &&
    $Heap#SameReachableFromParams#1($h_0, $x1_0, $h_1, $x1_1) &&
    $Heap#SameReachableFromParams#1($h_0, $x2_0, $h_1, $x2_1) &&
    $Heap#SameReachableFromParams#1($h_0, $x3_0, $h_1, $x3_1)
}

function $Heap#SameReachableFromParams#2($h_0:Heap, $x0_0,$x1_0:Ref, $h_1:Heap, $x0_1,$x1_1:Ref) : bool
{
	$Heap#SameReachableFromParams#1($h_0, $x0_0, $h_1, $x0_1) &&
    $Heap#SameReachableFromParams#1($h_0, $x1_0, $h_1, $x1_1)
} 

function $Heap#SameReachableFromParams#1($h_0:Heap, $x0_0:Ref, $h_1:Heap, $x0_1:Ref) : bool 
{
	(forall $a:Ref :: {$Written($h_0,$a)} {$Written($h_1,$a)}
		$Reach($h_0, $x0_0, $a) == $Reach($h_1, $x0_1, $a)) 
}

/////////////////////////////////////////////////////////////////////////////
// Isomorphism
function $Isomorphism($h_1, $h_2:Heap, $roots:Roots) : bool;

// equal heaps are isomorphic
axiom (forall $heap:Heap, $roots:Roots :: {$Isomorphism($heap, $heap, $roots)}
			$GoodHeap($heap) &&
			$Roots#Allocated($roots, $heap)
		==> 
			$Isomorphism($heap, $heap, $roots));

// extensionally equal heaps are isomorphic
axiom (forall $h_1,$h_2:Heap, $roots:Roots :: {$Isomorphism($h_1, $h_2, $roots)} 
			$Roots#Allocated($roots, $h_1) && 
			$Heap#Equal($h_1, $h_2)   
		==> 
			$Isomorphism($h_1, $h_2, $roots));

// extensionally equal reachable heaps are isomorphic
axiom (forall $h_1,$h_2:Heap, $roots:Roots :: {$Isomorphism($h_1, $h_2, $roots)} 
			   $Roots#Allocated($roots, $h_1)
			&& $Heap#ReachableEqual($h_1, $h_2, $roots)   
		==> 
			$Isomorphism($h_1, $h_2, $roots));

///////////////////////////////////////////////////////


// abstraction of function behaviour
function $abs_Caller_0($strategy:int, $h_pre:Heap, x_0:Ref,r_0:Ref, $h_post:Heap):bool;

// version _0 of the procedure
procedure Caller_0($strategy:int, $h:Heap, $roots:Roots, x:Ref,r:Ref) returns ($h_0:Heap)
    requires $Allocated($h, x) && $Allocated($h, r);
    requires $GoodHeap($h);
    requires $GoodRoots($roots);
    requires $Roots#Allocated($roots, $h);
    free ensures (forall $a:Ref :: $Reachable($h_0, $roots, $a) ==> $Allocated($h_0, $a)); // should be an axiom of well formed heaps
    free ensures $GoodHeap($h_0);
    free ensures $HeapSucc($h, $h_0); // this maybe introduces performance issues
    free ensures $abs_Caller_0($strategy, $h, x, r, $h_0);
    free ensures $Heap#Bigger($h, $h_0);
    free ensures (forall $a:Ref :: // stuff is not pulled out of the garbage
					$Reachable($h_0, $roots, $a) ==>
						$Reachable($h, $roots, $a) || 
						!$Allocated($h, $a) || 
						$ReachableFromParams#2($h , x, r, $a)); 
	free ensures (forall <alpha> $a:Ref,$f:Field alpha :: // only reachable stuff is modified 
					$a != $Null && $Allocated($h,$a) && $Read($h,$a,$f)!=$Read($h_0,$a,$f) ==> 
						$ReachableFromParams#2($h , x, r, $a));

    ensures (forall <alpha> $a:Ref,$f:Field alpha :: {$Read($h_0,$a,$f)}
       $a != $Null && $Allocated($h,$a) 
       ==> 
       $Read($h,$a,$f)==$Read($h_0,$a,$f) || $a==r 
    );

    free ensures (forall $a:Ref :: // stuff is made reachable only if something in the modifies set is reachable
    				$Reachable($h_0, $roots, $a) && !$Reachable($h, $roots, $a) ==>
    				    $Allocated($h_0, $a) &&
    					($Reachable($h, $roots, r ))
    );

    free ensures (forall $a:Ref :: // stuff is made reachable only if something in the modifies set is reachable
    				$ReachableFromParams#1($h_0, x, $a) && !$ReachableFromParams#1($h, x, $a) ==>
    				    $Allocated($h_0, $a) &&
    					($ReachableFromParams#1($h, x, r ))
    );
    free ensures (forall $a:Ref :: // stuff is made reachable only if something in the modifies set is reachable
    				$ReachableFromParams#1($h_0, r, $a) && !$ReachableFromParams#1($h, r, $a) ==>
    				    $Allocated($h_0, $a) &&
    					($ReachableFromParams#1($h, r, r ))
    );
     
{
    // declare locals
	var $a#0_0:Ref;
	var $a#1_0:Ref;
	var $t#0_0:Ref;
	var $t#1_0:Ref;
	var $t#2_0:Ref;
	var $t#3_0:Ref;
	var $t#4_0:Ref;
	var $t#5_0:Ref;
	var r0_0:Ref;
	var r1_0:Ref;
	var r_0:Ref;
	var t0_0:Ref;
	var t1_0:Ref;
	var x_0:Ref;
	$h_0 := $h;

	// initialise locals
	$a#0_0 := $Null;
	$a#1_0 := $Null;
	$t#0_0 := $Null;
	$t#1_0 := $Null;
	$t#2_0 := $Null;
	$t#3_0 := $Null;
	$t#4_0 := $Null;
	$t#5_0 := $Null;
	r0_0 := $Null;
	r1_0 := $Null;
	r_0 := $Null;
	t0_0 := $Null;
	t1_0 := $Null;
	x_0 := $Null;

			// inline statements
			x_0 := x ;
			assume $ReadObject($h_0, x);
			r_0 := r ;
			assume $ReadObject($h_0, r);
			if((x_0  != $Null ) )
			{
				$t#0_0 := $a#0_0 ;
				assume $ReadObject($h_0, $a#0_0);
				r0_0 := $t#0_0 ;
				assume $ReadObject($h_0, $t#0_0);
				$t#1_0 := $a#1_0 ;
				assume $ReadObject($h_0, $a#1_0);
				r1_0 := $t#1_0 ;
				assume $ReadObject($h_0, $t#1_0);
				$t#2_0 := $Read($h_0,x_0,$field#f) ;
				assume $ReadObject($h_0, x_0);
				assume $ReadObject($h_0, $Read($h_0,x_0,$field#f) );
				t0_0 := $t#2_0 ;
				assume $ReadObject($h_0, $t#2_0);
				 call $h_0:=Caller_0(0, $h_0, $roots, t0_0, r0_0); 
				$t#3_0 := $Read($h_0,x_0,$field#g) ;
				assume $ReadObject($h_0, x_0);
				assume $ReadObject($h_0, $Read($h_0,x_0,$field#g) );
				t1_0 := $t#3_0 ;
				assume $ReadObject($h_0, $t#3_0);
				 call $h_0:=Caller_0(0, $h_0, $roots, t1_0, r1_0); 
				$t#4_0 := $Read($h_0,r0_0,$field#v) ;
				assume $ReadObject($h_0, r0_0);
				assume $ReadObject($h_0, $Read($h_0,r0_0,$field#v) );
				$h_0:=$Write($h_0,r_0,$field#f,$t#4_0); assume $GoodHeap($h_0);
				$t#5_0 := $Read($h_0,r1_0,$field#v) ;
				assume $ReadObject($h_0, r1_0);
				assume $ReadObject($h_0, $Read($h_0,r1_0,$field#v) );
				$h_0:=$Write($h_0,r_0,$field#g,$t#5_0); assume $GoodHeap($h_0);
			}
			else
			{

			}


}

// abstraction of function behaviour
function $abs_Caller_1($strategy:int, $h_pre:Heap, x_1:Ref,r_1:Ref, $h_post:Heap):bool;

// version _1 of the procedure
procedure Caller_1($strategy:int, $h:Heap, $roots:Roots, x:Ref,r:Ref) returns ($h_1:Heap)
    requires $Allocated($h, x) && $Allocated($h, r);
    requires $GoodHeap($h);
    requires $GoodRoots($roots);
    requires $Roots#Allocated($roots, $h);
    free ensures (forall $a:Ref :: $Reachable($h_1, $roots, $a) ==> $Allocated($h_1, $a)); // should be an axiom of well formed heaps
    free ensures $GoodHeap($h_1);
    free ensures $HeapSucc($h, $h_1); // this maybe introduces performance issues
    free ensures $abs_Caller_1($strategy, $h, x, r, $h_1);
    free ensures $Heap#Bigger($h, $h_1);
    free ensures (forall $a:Ref :: // stuff is not pulled out of the garbage
					$Reachable($h_1, $roots, $a) ==>
						$Reachable($h, $roots, $a) || 
						!$Allocated($h, $a) || 
						$ReachableFromParams#2($h , x, r, $a)); 
	free ensures (forall <alpha> $a:Ref,$f:Field alpha :: // only reachable stuff is modified 
					$a != $Null && $Allocated($h,$a) && $Read($h,$a,$f)!=$Read($h_1,$a,$f) ==> 
						$ReachableFromParams#2($h , x, r, $a));

    ensures (forall <alpha> $a:Ref,$f:Field alpha :: {$Read($h_1,$a,$f)}
       $a != $Null && $Allocated($h,$a) 
       ==> 
       $Read($h,$a,$f)==$Read($h_1,$a,$f) || $a==r 
    );

    free ensures (forall $a:Ref :: // stuff is made reachable only if something in the modifies set is reachable
    				$Reachable($h_1, $roots, $a) && !$Reachable($h, $roots, $a) ==>
    				    $Allocated($h_1, $a) &&
    					($Reachable($h, $roots, r ))
    );

    free ensures (forall $a:Ref :: // stuff is made reachable only if something in the modifies set is reachable
    				$ReachableFromParams#1($h_1, x, $a) && !$ReachableFromParams#1($h, x, $a) ==>
    				    $Allocated($h_1, $a) &&
    					($ReachableFromParams#1($h, x, r ))
    );
    free ensures (forall $a:Ref :: // stuff is made reachable only if something in the modifies set is reachable
    				$ReachableFromParams#1($h_1, r, $a) && !$ReachableFromParams#1($h, r, $a) ==>
    				    $Allocated($h_1, $a) &&
    					($ReachableFromParams#1($h, r, r ))
    );
     
{
    // declare locals
	var $a#0_1:Ref;
	var $a#1_1:Ref;
	var $t#0_1:Ref;
	var $t#1_1:Ref;
	var $t#2_1:Ref;
	var $t#3_1:Ref;
	var $t#4_1:Ref;
	var $t#5_1:Ref;
	var r0_1:Ref;
	var r1_1:Ref;
	var r_1:Ref;
	var t0_1:Ref;
	var t1_1:Ref;
	var x_1:Ref;
	$h_1 := $h;

	// initialise locals
	$a#0_1 := $Null;
	$a#1_1 := $Null;
	$t#0_1 := $Null;
	$t#1_1 := $Null;
	$t#2_1 := $Null;
	$t#3_1 := $Null;
	$t#4_1 := $Null;
	$t#5_1 := $Null;
	r0_1 := $Null;
	r1_1 := $Null;
	r_1 := $Null;
	t0_1 := $Null;
	t1_1 := $Null;
	x_1 := $Null;

			// inline statements
			x_1 := x ;
			assume $ReadObject($h_1, x);
			r_1 := r ;
			assume $ReadObject($h_1, r);
			if((x_1  != $Null ) )
			{
				$t#0_1 := $a#0_1 ;
				assume $ReadObject($h_1, $a#0_1);
				r0_1 := $t#0_1 ;
				assume $ReadObject($h_1, $t#0_1);
				$t#1_1 := $a#1_1 ;
				assume $ReadObject($h_1, $a#1_1);
				r1_1 := $t#1_1 ;
				assume $ReadObject($h_1, $t#1_1);
				$t#2_1 := $Read($h_1,x_1,$field#g) ;
				assume $ReadObject($h_1, x_1);
				assume $ReadObject($h_1, $Read($h_1,x_1,$field#g) );
				t0_1 := $t#2_1 ;
				assume $ReadObject($h_1, $t#2_1);
				 call $h_1:=Caller_1(0, $h_1, $roots, t0_1, r0_1); 
				$t#3_1 := $Read($h_1,x_1,$field#f) ;
				assume $ReadObject($h_1, x_1);
				assume $ReadObject($h_1, $Read($h_1,x_1,$field#f) );
				t1_1 := $t#3_1 ;
				assume $ReadObject($h_1, $t#3_1);
				 call $h_1:=Caller_1(0, $h_1, $roots, t1_1, r1_1); 
				$t#4_1 := $Read($h_1,r0_1,$field#v) ;
				assume $ReadObject($h_1, r0_1);
				assume $ReadObject($h_1, $Read($h_1,r0_1,$field#v) );
				$h_1:=$Write($h_1,r_1,$field#g,$t#4_1); assume $GoodHeap($h_1);
				$t#5_1 := $Read($h_1,r1_1,$field#v) ;
				assume $ReadObject($h_1, r1_1);
				assume $ReadObject($h_1, $Read($h_1,r1_1,$field#v) );
				$h_1:=$Write($h_1,r_1,$field#f,$t#5_1); assume $GoodHeap($h_1);
			}
			else
			{

			}


}

// mutual summary class com.lexicalscope.bl.equiv.ProcedurePair
axiom (forall 
            $allocator:int,
            $h0_0:Heap, x_0:Ref,r_0:Ref, $hn_0:Heap,
			$h0_1:Heap, x_1:Ref,r_1:Ref, $hn_1:Heap ::
			{
				$abs_Caller_0($allocator, $h0_0 , x_0, r_0, $hn_0) ,
				$abs_Caller_1($allocator, $h0_1 , x_1, r_1, $hn_1) 
			}
			$abs_Caller_0($allocator, $h0_0 , x_0, r_0, $hn_0) &&
			$abs_Caller_1($allocator, $h0_1 , x_1, r_1, $hn_1) &&
			$Heap#EqualFromParams#2($h0_0 , x_0, r_0, $h0_1 , x_1, r_1) ==>
			$Heap#EqualFromParams#2($hn_0 , x_0, r_0, $hn_1 , x_1, r_1) &&
			$Heap#SameReachableFromParams#2($hn_0 , x_0, r_0, $hn_1 , x_1, r_1) &&
			$SameDiff($h0_0, $hn_0, $h0_1, $hn_1));


// product procedure
procedure Caller_Caller($h:Heap, $roots:Roots, x:Ref,r:Ref)
    requires $GoodHeap($h);
    requires $GoodRoots($roots);
	requires $Roots#Allocated($roots, $h);
	requires $Allocated($h, x) && $Allocated($h, r);
	requires (forall $a:Ref :: $Allocated($h, $a) == $Root($roots, $a));
	requires $Roots#EverythingAllocatedIsARoot($roots, $h);
	requires (forall $a:Ref :: $Reachable($h, $roots, $a) ==> $Allocated($h, $a)); // should be an axiom of well formed heaps
{
			// declare locals for strategy 0
			// locals for version _0
			var $a#0_0$0:Ref;
			var $a#1_0$0:Ref;
			var $t#0_0$0:Ref;
			var $t#1_0$0:Ref;
			var $t#2_0$0:Ref;
			var $t#3_0$0:Ref;
			var $t#4_0$0:Ref;
			var $t#5_0$0:Ref;
			var r0_0$0:Ref;
			var r1_0$0:Ref;
			var r_0$0:Ref;
			var t0_0$0:Ref;
			var t1_0$0:Ref;
			var x_0$0:Ref;
			var $h_0$0:Heap;
			// locals for version _1
			var $a#0_1$0:Ref;
			var $a#1_1$0:Ref;
			var $t#0_1$0:Ref;
			var $t#1_1$0:Ref;
			var $t#2_1$0:Ref;
			var $t#3_1$0:Ref;
			var $t#4_1$0:Ref;
			var $t#5_1$0:Ref;
			var r0_1$0:Ref;
			var r1_1$0:Ref;
			var r_1$0:Ref;
			var t0_1$0:Ref;
			var t1_1$0:Ref;
			var x_1$0:Ref;
			var $h_1$0:Heap;

			// declare copies of parameters for allocation strategy
			var x$0:Ref;
			var r$0:Ref;
			// declare locals for strategy 1
			// locals for version _0
			var $a#0_0$1:Ref;
			var $a#1_0$1:Ref;
			var $t#0_0$1:Ref;
			var $t#1_0$1:Ref;
			var $t#2_0$1:Ref;
			var $t#3_0$1:Ref;
			var $t#4_0$1:Ref;
			var $t#5_0$1:Ref;
			var r0_0$1:Ref;
			var r1_0$1:Ref;
			var r_0$1:Ref;
			var t0_0$1:Ref;
			var t1_0$1:Ref;
			var x_0$1:Ref;
			var $h_0$1:Heap;
			// locals for version _1
			var $a#0_1$1:Ref;
			var $a#1_1$1:Ref;
			var $t#0_1$1:Ref;
			var $t#1_1$1:Ref;
			var $t#2_1$1:Ref;
			var $t#3_1$1:Ref;
			var $t#4_1$1:Ref;
			var $t#5_1$1:Ref;
			var r0_1$1:Ref;
			var r1_1$1:Ref;
			var r_1$1:Ref;
			var t0_1$1:Ref;
			var t1_1$1:Ref;
			var x_1$1:Ref;
			var $h_1$1:Heap;

			// declare copies of parameters for allocation strategy
			var x$1:Ref;
			var r$1:Ref;


			// initialise locals for strategy 0	

			// initialise locals for version _0
			$a#0_0$0 := $Null;
			$a#1_0$0 := $Null;
			$t#0_0$0 := $Null;
			$t#1_0$0 := $Null;
			$t#2_0$0 := $Null;
			$t#3_0$0 := $Null;
			$t#4_0$0 := $Null;
			$t#5_0$0 := $Null;
			r0_0$0 := $Null;
			r1_0$0 := $Null;
			r_0$0 := $Null;
			t0_0$0 := $Null;
			t1_0$0 := $Null;
			x_0$0 := $Null;

			// initialise locals for version _1
			$a#0_1$0 := $Null;
			$a#1_1$0 := $Null;
			$t#0_1$0 := $Null;
			$t#1_1$0 := $Null;
			$t#2_1$0 := $Null;
			$t#3_1$0 := $Null;
			$t#4_1$0 := $Null;
			$t#5_1$0 := $Null;
			r0_1$0 := $Null;
			r1_1$0 := $Null;
			r_1$0 := $Null;
			t0_1$0 := $Null;
			t1_1$0 := $Null;
			x_1$0 := $Null;
			// initialise locals for strategy 1	

			// initialise locals for version _0
			$a#0_0$1 := $Null;
			$a#1_0$1 := $Null;
			$t#0_0$1 := $Null;
			$t#1_0$1 := $Null;
			$t#2_0$1 := $Null;
			$t#3_0$1 := $Null;
			$t#4_0$1 := $Null;
			$t#5_0$1 := $Null;
			r0_0$1 := $Null;
			r1_0$1 := $Null;
			r_0$1 := $Null;
			t0_0$1 := $Null;
			t1_0$1 := $Null;
			x_0$1 := $Null;

			// initialise locals for version _1
			$a#0_1$1 := $Null;
			$a#1_1$1 := $Null;
			$t#0_1$1 := $Null;
			$t#1_1$1 := $Null;
			$t#2_1$1 := $Null;
			$t#3_1$1 := $Null;
			$t#4_1$1 := $Null;
			$t#5_1$1 := $Null;
			r0_1$1 := $Null;
			r1_1$1 := $Null;
			r_1$1 := $Null;
			t0_1$1 := $Null;
			t1_1$1 := $Null;
			x_1$1 := $Null;


    assume $ReadObject($h,x);
    assume $ReadObject($h,r);


		    // restore heaps
		    $h_0$0 := $h;
		    $h_1$0 := $h;

		    x$0 := x;
		    r$0 := r;

		    // prefix start
			havoc $a#0_0$0; assume !$Allocated($h_0$0,$a#0_0$0);
			$h_0$0:=$Allocate($h_0$0,$a#0_0$0); assume $GoodHeap($h_0$0);
			assume $AllocatedObject($h_0$0, $a#0_0$0);
			assert $FieldsNull($h_0$0, $a#0_0$0);
			assert $ReachNull($h_0$0, $a#0_0$0);
			havoc $a#1_0$0; assume !$Allocated($h_0$0,$a#1_0$0);
			$h_0$0:=$Allocate($h_0$0,$a#1_0$0); assume $GoodHeap($h_0$0);
			assume $AllocatedObject($h_0$0, $a#1_0$0);
			assert $FieldsNull($h_0$0, $a#1_0$0);
			assert $ReachNull($h_0$0, $a#1_0$0);
			havoc $a#0_1$0; assume !$Allocated($h_1$0,$a#0_1$0);
			$h_1$0:=$Allocate($h_1$0,$a#0_1$0); assume $GoodHeap($h_1$0);
			assume $AllocatedObject($h_1$0, $a#0_1$0);
			assert $FieldsNull($h_1$0, $a#0_1$0);
			assert $ReachNull($h_1$0, $a#0_1$0);
			havoc $a#1_1$0; assume !$Allocated($h_1$0,$a#1_1$0);
			$h_1$0:=$Allocate($h_1$0,$a#1_1$0); assume $GoodHeap($h_1$0);
			assume $AllocatedObject($h_1$0, $a#1_1$0);
			assert $FieldsNull($h_1$0, $a#1_1$0);
			assert $ReachNull($h_1$0, $a#1_1$0);

			// assert (forall $a:Ref :: $ReachableFromParams#1($h_0$0, $a#0_0$0, $a) ==> $a==$Null);

				assume $a#0_0$0 == $a#0_1$0;
				assume $a#1_0$0 == $a#1_1$0;

			// procedure body _0 start	
		    x_0$0 := x$0 ;
		    assume $ReadObject($h_0$0, x$0);
		    r_0$0 := r$0 ;
		    assume $ReadObject($h_0$0, r$0);
		    if((x_0$0  != $Null ) )
		    {
		    	$t#0_0$0 := $a#0_0$0 ;
		    	assume $ReadObject($h_0$0, $a#0_0$0);
		    	r0_0$0 := $t#0_0$0 ;
		    	assume $ReadObject($h_0$0, $t#0_0$0);
		    	$t#1_0$0 := $a#1_0$0 ;
		    	assume $ReadObject($h_0$0, $a#1_0$0);
		    	r1_0$0 := $t#1_0$0 ;
		    	assume $ReadObject($h_0$0, $t#1_0$0);
		    	$t#2_0$0 := $Read($h_0$0,x_0$0,$field#f) ;
		    	assume $ReadObject($h_0$0, x_0$0);
		    	assume $ReadObject($h_0$0, $Read($h_0$0,x_0$0,$field#f) );
		    	t0_0$0 := $t#2_0$0 ;
		    	assume $ReadObject($h_0$0, $t#2_0$0);
		    	 call $h_0$0:=Caller_0(0, $h_0$0, $roots, t0_0$0, r0_0$0); 
		    	$t#3_0$0 := $Read($h_0$0,x_0$0,$field#g) ;
		    	assume $ReadObject($h_0$0, x_0$0);
		    	assume $ReadObject($h_0$0, $Read($h_0$0,x_0$0,$field#g) );
		    	t1_0$0 := $t#3_0$0 ;
		    	assume $ReadObject($h_0$0, $t#3_0$0);
		    	 call $h_0$0:=Caller_0(0, $h_0$0, $roots, t1_0$0, r1_0$0); 
		    	$t#4_0$0 := $Read($h_0$0,r0_0$0,$field#v) ;
		    	assume $ReadObject($h_0$0, r0_0$0);
		    	assume $ReadObject($h_0$0, $Read($h_0$0,r0_0$0,$field#v) );
		    	$h_0$0:=$Write($h_0$0,r_0$0,$field#f,$t#4_0$0); assume $GoodHeap($h_0$0);
		    	$t#5_0$0 := $Read($h_0$0,r1_0$0,$field#v) ;
		    	assume $ReadObject($h_0$0, r1_0$0);
		    	assume $ReadObject($h_0$0, $Read($h_0$0,r1_0$0,$field#v) );
		    	$h_0$0:=$Write($h_0$0,r_0$0,$field#g,$t#5_0$0); assume $GoodHeap($h_0$0);
		    }
		    else
		    {

		    }


		    // procedure body _1 start
		    x_1$0 := x$0 ;
		    assume $ReadObject($h_1$0, x$0);
		    r_1$0 := r$0 ;
		    assume $ReadObject($h_1$0, r$0);
		    if((x_1$0  != $Null ) )
		    {
		    	$t#0_1$0 := $a#0_1$0 ;
		    	assume $ReadObject($h_1$0, $a#0_1$0);
		    	r0_1$0 := $t#0_1$0 ;
		    	assume $ReadObject($h_1$0, $t#0_1$0);
		    	$t#1_1$0 := $a#1_1$0 ;
		    	assume $ReadObject($h_1$0, $a#1_1$0);
		    	r1_1$0 := $t#1_1$0 ;
		    	assume $ReadObject($h_1$0, $t#1_1$0);
		    	$t#2_1$0 := $Read($h_1$0,x_1$0,$field#g) ;
		    	assume $ReadObject($h_1$0, x_1$0);
		    	assume $ReadObject($h_1$0, $Read($h_1$0,x_1$0,$field#g) );
		    	t0_1$0 := $t#2_1$0 ;
		    	assume $ReadObject($h_1$0, $t#2_1$0);
		    	 call $h_1$0:=Caller_1(0, $h_1$0, $roots, t0_1$0, r0_1$0); 
		    	$t#3_1$0 := $Read($h_1$0,x_1$0,$field#f) ;
		    	assume $ReadObject($h_1$0, x_1$0);
		    	assume $ReadObject($h_1$0, $Read($h_1$0,x_1$0,$field#f) );
		    	t1_1$0 := $t#3_1$0 ;
		    	assume $ReadObject($h_1$0, $t#3_1$0);
		    	 call $h_1$0:=Caller_1(0, $h_1$0, $roots, t1_1$0, r1_1$0); 
		    	$t#4_1$0 := $Read($h_1$0,r0_1$0,$field#v) ;
		    	assume $ReadObject($h_1$0, r0_1$0);
		    	assume $ReadObject($h_1$0, $Read($h_1$0,r0_1$0,$field#v) );
		    	$h_1$0:=$Write($h_1$0,r_1$0,$field#g,$t#4_1$0); assume $GoodHeap($h_1$0);
		    	$t#5_1$0 := $Read($h_1$0,r1_1$0,$field#v) ;
		    	assume $ReadObject($h_1$0, r1_1$0);
		    	assume $ReadObject($h_1$0, $Read($h_1$0,r1_1$0,$field#v) );
		    	$h_1$0:=$Write($h_1$0,r_1$0,$field#f,$t#5_1$0); assume $GoodHeap($h_1$0);
		    }
		    else
		    {

		    }


		    // restore heaps
		    $h_0$1 := $h;
		    $h_1$1 := $h;

		    x$1 := x;
		    r$1 := r;

		    // prefix start
			havoc $a#0_0$1; assume !$Allocated($h_0$1,$a#0_0$1);
			$h_0$1:=$Allocate($h_0$1,$a#0_0$1); assume $GoodHeap($h_0$1);
			assume $AllocatedObject($h_0$1, $a#0_0$1);
			assert $FieldsNull($h_0$1, $a#0_0$1);
			assert $ReachNull($h_0$1, $a#0_0$1);
			havoc $a#1_0$1; assume !$Allocated($h_0$1,$a#1_0$1);
			$h_0$1:=$Allocate($h_0$1,$a#1_0$1); assume $GoodHeap($h_0$1);
			assume $AllocatedObject($h_0$1, $a#1_0$1);
			assert $FieldsNull($h_0$1, $a#1_0$1);
			assert $ReachNull($h_0$1, $a#1_0$1);
			havoc $a#0_1$1; assume !$Allocated($h_1$1,$a#0_1$1);
			$h_1$1:=$Allocate($h_1$1,$a#0_1$1); assume $GoodHeap($h_1$1);
			assume $AllocatedObject($h_1$1, $a#0_1$1);
			assert $FieldsNull($h_1$1, $a#0_1$1);
			assert $ReachNull($h_1$1, $a#0_1$1);
			havoc $a#1_1$1; assume !$Allocated($h_1$1,$a#1_1$1);
			$h_1$1:=$Allocate($h_1$1,$a#1_1$1); assume $GoodHeap($h_1$1);
			assume $AllocatedObject($h_1$1, $a#1_1$1);
			assert $FieldsNull($h_1$1, $a#1_1$1);
			assert $ReachNull($h_1$1, $a#1_1$1);

			// assert (forall $a:Ref :: $ReachableFromParams#1($h_0$0, $a#0_0$0, $a) ==> $a==$Null);

				assume $a#1_0$1 == $a#0_1$1;
				assume $a#0_0$1 == $a#1_1$1;

			// procedure body _0 start	
		    x_0$1 := x$1 ;
		    assume $ReadObject($h_0$1, x$1);
		    r_0$1 := r$1 ;
		    assume $ReadObject($h_0$1, r$1);
		    if((x_0$1  != $Null ) )
		    {
		    	$t#0_0$1 := $a#0_0$1 ;
		    	assume $ReadObject($h_0$1, $a#0_0$1);
		    	r0_0$1 := $t#0_0$1 ;
		    	assume $ReadObject($h_0$1, $t#0_0$1);
		    	$t#1_0$1 := $a#1_0$1 ;
		    	assume $ReadObject($h_0$1, $a#1_0$1);
		    	r1_0$1 := $t#1_0$1 ;
		    	assume $ReadObject($h_0$1, $t#1_0$1);
		    	$t#2_0$1 := $Read($h_0$1,x_0$1,$field#f) ;
		    	assume $ReadObject($h_0$1, x_0$1);
		    	assume $ReadObject($h_0$1, $Read($h_0$1,x_0$1,$field#f) );
		    	t0_0$1 := $t#2_0$1 ;
		    	assume $ReadObject($h_0$1, $t#2_0$1);
		    	 call $h_0$1:=Caller_0(1, $h_0$1, $roots, t0_0$1, r0_0$1); 
		    	$t#3_0$1 := $Read($h_0$1,x_0$1,$field#g) ;
		    	assume $ReadObject($h_0$1, x_0$1);
		    	assume $ReadObject($h_0$1, $Read($h_0$1,x_0$1,$field#g) );
		    	t1_0$1 := $t#3_0$1 ;
		    	assume $ReadObject($h_0$1, $t#3_0$1);
		    	 call $h_0$1:=Caller_0(1, $h_0$1, $roots, t1_0$1, r1_0$1); 
		    	$t#4_0$1 := $Read($h_0$1,r0_0$1,$field#v) ;
		    	assume $ReadObject($h_0$1, r0_0$1);
		    	assume $ReadObject($h_0$1, $Read($h_0$1,r0_0$1,$field#v) );
		    	$h_0$1:=$Write($h_0$1,r_0$1,$field#f,$t#4_0$1); assume $GoodHeap($h_0$1);
		    	$t#5_0$1 := $Read($h_0$1,r1_0$1,$field#v) ;
		    	assume $ReadObject($h_0$1, r1_0$1);
		    	assume $ReadObject($h_0$1, $Read($h_0$1,r1_0$1,$field#v) );
		    	$h_0$1:=$Write($h_0$1,r_0$1,$field#g,$t#5_0$1); assume $GoodHeap($h_0$1);
		    }
		    else
		    {

		    }


		    // procedure body _1 start
		    x_1$1 := x$1 ;
		    assume $ReadObject($h_1$1, x$1);
		    r_1$1 := r$1 ;
		    assume $ReadObject($h_1$1, r$1);
		    if((x_1$1  != $Null ) )
		    {
		    	$t#0_1$1 := $a#0_1$1 ;
		    	assume $ReadObject($h_1$1, $a#0_1$1);
		    	r0_1$1 := $t#0_1$1 ;
		    	assume $ReadObject($h_1$1, $t#0_1$1);
		    	$t#1_1$1 := $a#1_1$1 ;
		    	assume $ReadObject($h_1$1, $a#1_1$1);
		    	r1_1$1 := $t#1_1$1 ;
		    	assume $ReadObject($h_1$1, $t#1_1$1);
		    	$t#2_1$1 := $Read($h_1$1,x_1$1,$field#g) ;
		    	assume $ReadObject($h_1$1, x_1$1);
		    	assume $ReadObject($h_1$1, $Read($h_1$1,x_1$1,$field#g) );
		    	t0_1$1 := $t#2_1$1 ;
		    	assume $ReadObject($h_1$1, $t#2_1$1);
		    	 call $h_1$1:=Caller_1(1, $h_1$1, $roots, t0_1$1, r0_1$1); 
		    	$t#3_1$1 := $Read($h_1$1,x_1$1,$field#f) ;
		    	assume $ReadObject($h_1$1, x_1$1);
		    	assume $ReadObject($h_1$1, $Read($h_1$1,x_1$1,$field#f) );
		    	t1_1$1 := $t#3_1$1 ;
		    	assume $ReadObject($h_1$1, $t#3_1$1);
		    	 call $h_1$1:=Caller_1(1, $h_1$1, $roots, t1_1$1, r1_1$1); 
		    	$t#4_1$1 := $Read($h_1$1,r0_1$1,$field#v) ;
		    	assume $ReadObject($h_1$1, r0_1$1);
		    	assume $ReadObject($h_1$1, $Read($h_1$1,r0_1$1,$field#v) );
		    	$h_1$1:=$Write($h_1$1,r_1$1,$field#g,$t#4_1$1); assume $GoodHeap($h_1$1);
		    	$t#5_1$1 := $Read($h_1$1,r1_1$1,$field#v) ;
		    	assume $ReadObject($h_1$1, r1_1$1);
		    	assume $ReadObject($h_1$1, $Read($h_1$1,r1_1$1,$field#v) );
		    	$h_1$1:=$Write($h_1$1,r_1$1,$field#f,$t#5_1$1); assume $GoodHeap($h_1$1);
		    }
		    else
		    {

		    }



	assert 
		$Isomorphism($h_0$0, $h_1$0, $roots) ||
		$Isomorphism($h_0$1, $h_1$1, $roots);	
}