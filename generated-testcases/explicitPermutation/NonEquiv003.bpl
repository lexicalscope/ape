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
function $abs_G_0($strategy:int, $h_pre:Heap, x_0:Ref,y_0:Ref, $h_post:Heap):bool;

// version _0 of the procedure
procedure G_0($strategy:int, $h:Heap, $roots:Roots, x:Ref,y:Ref) returns ($h_0:Heap)
    requires $Allocated($h, x) && $Allocated($h, y);
    requires $GoodHeap($h);
    requires $GoodRoots($roots);
    requires $Roots#Allocated($roots, $h);
    free ensures (forall $a:Ref :: $Reachable($h_0, $roots, $a) ==> $Allocated($h_0, $a)); // should be an axiom of well formed heaps
    free ensures $GoodHeap($h_0);
    free ensures $HeapSucc($h, $h_0); // this maybe introduces performance issues
    free ensures $abs_G_0($strategy, $h, x, y, $h_0);
    free ensures $Heap#Bigger($h, $h_0);
    free ensures (forall $a:Ref :: // stuff is not pulled out of the garbage
					$Reachable($h_0, $roots, $a) ==>
						$Reachable($h, $roots, $a) || 
						!$Allocated($h, $a) || 
						$ReachableFromParams#2($h , x, y, $a)); 
	free ensures (forall <alpha> $a:Ref,$f:Field alpha :: // only reachable stuff is modified 
					$a != $Null && $Allocated($h,$a) && $Read($h,$a,$f)!=$Read($h_0,$a,$f) ==> 
						$ReachableFromParams#2($h , x, y, $a));
     /* modifies anything */  
{
    // declare locals
	var $a#0_0:Ref;
	var $a#1_0:Ref;
	var $a#2_0:Ref;
	var $a#3_0:Ref;
	var $t#0_0:Ref;
	var $t#1_0:Ref;
	var $t#2_0:Ref;
	var n_0:Ref;
	var x_0:Ref;
	var xn_0:Ref;
	var y_0:Ref;
	var yn_0:Ref;
	$h_0 := $h;

	// initialise locals
	$a#0_0 := $Null;
	$a#1_0 := $Null;
	$a#2_0 := $Null;
	$a#3_0 := $Null;
	$t#0_0 := $Null;
	$t#1_0 := $Null;
	$t#2_0 := $Null;
	n_0 := $Null;
	x_0 := $Null;
	xn_0 := $Null;
	y_0 := $Null;
	yn_0 := $Null;

			// inline statements
			x_0 := x ;
			assume $ReadObject($h_0, x);
			y_0 := y ;
			assume $ReadObject($h_0, y);
			if(true )
			{
				$t#0_0 := $a#0_0 ;
				assume $ReadObject($h_0, $a#0_0);
			}
			if(true )
			{
				xn_0 := $t#0_0 ;
				assume $ReadObject($h_0, $t#0_0);
			}
			if(true )
			{
				$h_0:=$Write($h_0,x_0,$field#v,xn_0); assume $GoodHeap($h_0);
			}
			if(true )
			{
				$t#1_0 := $a#1_0 ;
				assume $ReadObject($h_0, $a#1_0);
			}
			if(true )
			{
				yn_0 := $t#1_0 ;
				assume $ReadObject($h_0, $t#1_0);
			}
			if(true )
			{
				$h_0:=$Write($h_0,y_0,$field#v,yn_0); assume $GoodHeap($h_0);
			}
			if(true )
			{
				$t#2_0 := $a#2_0 ;
				assume $ReadObject($h_0, $a#2_0);
			}
			if(true )
			{
				n_0 := $t#2_0 ;
				assume $ReadObject($h_0, $t#2_0);
			}
			if(true )
			{
				$h_0:=$Write($h_0,yn_0,$field#v,n_0); assume $GoodHeap($h_0);
			}
			if(true )
			{
				$h_0:=$Write($h_0,xn_0,$field#v,n_0); assume $GoodHeap($h_0);
			}

}

// abstraction of function behaviour
function $abs_G_1($strategy:int, $h_pre:Heap, x_1:Ref,y_1:Ref, $h_post:Heap):bool;

// version _1 of the procedure
procedure G_1($strategy:int, $h:Heap, $roots:Roots, x:Ref,y:Ref) returns ($h_1:Heap)
    requires $Allocated($h, x) && $Allocated($h, y);
    requires $GoodHeap($h);
    requires $GoodRoots($roots);
    requires $Roots#Allocated($roots, $h);
    free ensures (forall $a:Ref :: $Reachable($h_1, $roots, $a) ==> $Allocated($h_1, $a)); // should be an axiom of well formed heaps
    free ensures $GoodHeap($h_1);
    free ensures $HeapSucc($h, $h_1); // this maybe introduces performance issues
    free ensures $abs_G_1($strategy, $h, x, y, $h_1);
    free ensures $Heap#Bigger($h, $h_1);
    free ensures (forall $a:Ref :: // stuff is not pulled out of the garbage
					$Reachable($h_1, $roots, $a) ==>
						$Reachable($h, $roots, $a) || 
						!$Allocated($h, $a) || 
						$ReachableFromParams#2($h , x, y, $a)); 
	free ensures (forall <alpha> $a:Ref,$f:Field alpha :: // only reachable stuff is modified 
					$a != $Null && $Allocated($h,$a) && $Read($h,$a,$f)!=$Read($h_1,$a,$f) ==> 
						$ReachableFromParams#2($h , x, y, $a));
     /* modifies anything */  
{
    // declare locals
	var $a#0_1:Ref;
	var $a#1_1:Ref;
	var $a#2_1:Ref;
	var $a#3_1:Ref;
	var $t#0_1:Ref;
	var $t#1_1:Ref;
	var $t#2_1:Ref;
	var $t#3_1:Ref;
	var x_1:Ref;
	var xn_1:Ref;
	var xnn_1:Ref;
	var y_1:Ref;
	var yn_1:Ref;
	var ynn_1:Ref;
	$h_1 := $h;

	// initialise locals
	$a#0_1 := $Null;
	$a#1_1 := $Null;
	$a#2_1 := $Null;
	$a#3_1 := $Null;
	$t#0_1 := $Null;
	$t#1_1 := $Null;
	$t#2_1 := $Null;
	$t#3_1 := $Null;
	x_1 := $Null;
	xn_1 := $Null;
	xnn_1 := $Null;
	y_1 := $Null;
	yn_1 := $Null;
	ynn_1 := $Null;

			// inline statements
			x_1 := x ;
			assume $ReadObject($h_1, x);
			y_1 := y ;
			assume $ReadObject($h_1, y);
			if(true )
			{
				$t#0_1 := $a#0_1 ;
				assume $ReadObject($h_1, $a#0_1);
			}
			if(true )
			{
				xn_1 := $t#0_1 ;
				assume $ReadObject($h_1, $t#0_1);
			}
			if(true )
			{
				$h_1:=$Write($h_1,x_1,$field#v,xn_1); assume $GoodHeap($h_1);
			}
			if(true )
			{
				$t#1_1 := $a#1_1 ;
				assume $ReadObject($h_1, $a#1_1);
			}
			if(true )
			{
				yn_1 := $t#1_1 ;
				assume $ReadObject($h_1, $t#1_1);
			}
			if(true )
			{
				$h_1:=$Write($h_1,y_1,$field#v,yn_1); assume $GoodHeap($h_1);
			}
			if(true )
			{
				$t#2_1 := $a#2_1 ;
				assume $ReadObject($h_1, $a#2_1);
			}
			if(true )
			{
				xnn_1 := $t#2_1 ;
				assume $ReadObject($h_1, $t#2_1);
			}
			if(true )
			{
				$t#3_1 := $a#3_1 ;
				assume $ReadObject($h_1, $a#3_1);
			}
			if(true )
			{
				ynn_1 := $t#3_1 ;
				assume $ReadObject($h_1, $t#3_1);
			}
			if(true )
			{
				$h_1:=$Write($h_1,yn_1,$field#v,ynn_1); assume $GoodHeap($h_1);
			}
			if(true )
			{
				$h_1:=$Write($h_1,xn_1,$field#v,xnn_1); assume $GoodHeap($h_1);
			}

}

// mutual summary class com.lexicalscope.bl.equiv.ProcedurePair
axiom (forall 
            $allocator:int,
            $h0_0:Heap, x_0:Ref,y_0:Ref, $hn_0:Heap,
			$h0_1:Heap, x_1:Ref,y_1:Ref, $hn_1:Heap ::
			{
				$abs_G_0($allocator, $h0_0 , x_0, y_0, $hn_0) ,
				$abs_G_1($allocator, $h0_1 , x_1, y_1, $hn_1) 
			}
			$abs_G_0($allocator, $h0_0 , x_0, y_0, $hn_0) &&
			$abs_G_1($allocator, $h0_1 , x_1, y_1, $hn_1) &&
			$Heap#EqualFromParams#2($h0_0 , x_0, y_0, $h0_1 , x_1, y_1) ==>
			$Heap#EqualFromParams#2($hn_0 , x_0, y_0, $hn_1 , x_1, y_1) &&
			$Heap#SameReachableFromParams#2($hn_0 , x_0, y_0, $hn_1 , x_1, y_1) &&
			$SameDiff($h0_0, $hn_0, $h0_1, $hn_1));


// product procedure
procedure G_G($h:Heap, $roots:Roots, x:Ref,y:Ref)
    requires $GoodHeap($h);
    requires $GoodRoots($roots);
	requires $Roots#Allocated($roots, $h);
	requires $Allocated($h, x) && $Allocated($h, y);
	requires (forall $a:Ref :: $Allocated($h, $a) == $Root($roots, $a));
	requires $Roots#EverythingAllocatedIsARoot($roots, $h);
	requires (forall $a:Ref :: $Reachable($h, $roots, $a) ==> $Allocated($h, $a)); // should be an axiom of well formed heaps
{
			// declare locals for strategy 0
			// locals for version _0
			var $a#0_0$0:Ref;
			var $a#1_0$0:Ref;
			var $a#2_0$0:Ref;
			var $a#3_0$0:Ref;
			var $t#0_0$0:Ref;
			var $t#1_0$0:Ref;
			var $t#2_0$0:Ref;
			var n_0$0:Ref;
			var x_0$0:Ref;
			var xn_0$0:Ref;
			var y_0$0:Ref;
			var yn_0$0:Ref;
			var $h_0$0:Heap;
			// locals for version _1
			var $a#0_1$0:Ref;
			var $a#1_1$0:Ref;
			var $a#2_1$0:Ref;
			var $a#3_1$0:Ref;
			var $t#0_1$0:Ref;
			var $t#1_1$0:Ref;
			var $t#2_1$0:Ref;
			var $t#3_1$0:Ref;
			var x_1$0:Ref;
			var xn_1$0:Ref;
			var xnn_1$0:Ref;
			var y_1$0:Ref;
			var yn_1$0:Ref;
			var ynn_1$0:Ref;
			var $h_1$0:Heap;

			// declare copies of parameters for allocation strategy
			var x$0:Ref;
			var y$0:Ref;
			// declare locals for strategy 1
			// locals for version _0
			var $a#0_0$1:Ref;
			var $a#1_0$1:Ref;
			var $a#2_0$1:Ref;
			var $a#3_0$1:Ref;
			var $t#0_0$1:Ref;
			var $t#1_0$1:Ref;
			var $t#2_0$1:Ref;
			var n_0$1:Ref;
			var x_0$1:Ref;
			var xn_0$1:Ref;
			var y_0$1:Ref;
			var yn_0$1:Ref;
			var $h_0$1:Heap;
			// locals for version _1
			var $a#0_1$1:Ref;
			var $a#1_1$1:Ref;
			var $a#2_1$1:Ref;
			var $a#3_1$1:Ref;
			var $t#0_1$1:Ref;
			var $t#1_1$1:Ref;
			var $t#2_1$1:Ref;
			var $t#3_1$1:Ref;
			var x_1$1:Ref;
			var xn_1$1:Ref;
			var xnn_1$1:Ref;
			var y_1$1:Ref;
			var yn_1$1:Ref;
			var ynn_1$1:Ref;
			var $h_1$1:Heap;

			// declare copies of parameters for allocation strategy
			var x$1:Ref;
			var y$1:Ref;
			// declare locals for strategy 2
			// locals for version _0
			var $a#0_0$2:Ref;
			var $a#1_0$2:Ref;
			var $a#2_0$2:Ref;
			var $a#3_0$2:Ref;
			var $t#0_0$2:Ref;
			var $t#1_0$2:Ref;
			var $t#2_0$2:Ref;
			var n_0$2:Ref;
			var x_0$2:Ref;
			var xn_0$2:Ref;
			var y_0$2:Ref;
			var yn_0$2:Ref;
			var $h_0$2:Heap;
			// locals for version _1
			var $a#0_1$2:Ref;
			var $a#1_1$2:Ref;
			var $a#2_1$2:Ref;
			var $a#3_1$2:Ref;
			var $t#0_1$2:Ref;
			var $t#1_1$2:Ref;
			var $t#2_1$2:Ref;
			var $t#3_1$2:Ref;
			var x_1$2:Ref;
			var xn_1$2:Ref;
			var xnn_1$2:Ref;
			var y_1$2:Ref;
			var yn_1$2:Ref;
			var ynn_1$2:Ref;
			var $h_1$2:Heap;

			// declare copies of parameters for allocation strategy
			var x$2:Ref;
			var y$2:Ref;
			// declare locals for strategy 3
			// locals for version _0
			var $a#0_0$3:Ref;
			var $a#1_0$3:Ref;
			var $a#2_0$3:Ref;
			var $a#3_0$3:Ref;
			var $t#0_0$3:Ref;
			var $t#1_0$3:Ref;
			var $t#2_0$3:Ref;
			var n_0$3:Ref;
			var x_0$3:Ref;
			var xn_0$3:Ref;
			var y_0$3:Ref;
			var yn_0$3:Ref;
			var $h_0$3:Heap;
			// locals for version _1
			var $a#0_1$3:Ref;
			var $a#1_1$3:Ref;
			var $a#2_1$3:Ref;
			var $a#3_1$3:Ref;
			var $t#0_1$3:Ref;
			var $t#1_1$3:Ref;
			var $t#2_1$3:Ref;
			var $t#3_1$3:Ref;
			var x_1$3:Ref;
			var xn_1$3:Ref;
			var xnn_1$3:Ref;
			var y_1$3:Ref;
			var yn_1$3:Ref;
			var ynn_1$3:Ref;
			var $h_1$3:Heap;

			// declare copies of parameters for allocation strategy
			var x$3:Ref;
			var y$3:Ref;
			// declare locals for strategy 4
			// locals for version _0
			var $a#0_0$4:Ref;
			var $a#1_0$4:Ref;
			var $a#2_0$4:Ref;
			var $a#3_0$4:Ref;
			var $t#0_0$4:Ref;
			var $t#1_0$4:Ref;
			var $t#2_0$4:Ref;
			var n_0$4:Ref;
			var x_0$4:Ref;
			var xn_0$4:Ref;
			var y_0$4:Ref;
			var yn_0$4:Ref;
			var $h_0$4:Heap;
			// locals for version _1
			var $a#0_1$4:Ref;
			var $a#1_1$4:Ref;
			var $a#2_1$4:Ref;
			var $a#3_1$4:Ref;
			var $t#0_1$4:Ref;
			var $t#1_1$4:Ref;
			var $t#2_1$4:Ref;
			var $t#3_1$4:Ref;
			var x_1$4:Ref;
			var xn_1$4:Ref;
			var xnn_1$4:Ref;
			var y_1$4:Ref;
			var yn_1$4:Ref;
			var ynn_1$4:Ref;
			var $h_1$4:Heap;

			// declare copies of parameters for allocation strategy
			var x$4:Ref;
			var y$4:Ref;
			// declare locals for strategy 5
			// locals for version _0
			var $a#0_0$5:Ref;
			var $a#1_0$5:Ref;
			var $a#2_0$5:Ref;
			var $a#3_0$5:Ref;
			var $t#0_0$5:Ref;
			var $t#1_0$5:Ref;
			var $t#2_0$5:Ref;
			var n_0$5:Ref;
			var x_0$5:Ref;
			var xn_0$5:Ref;
			var y_0$5:Ref;
			var yn_0$5:Ref;
			var $h_0$5:Heap;
			// locals for version _1
			var $a#0_1$5:Ref;
			var $a#1_1$5:Ref;
			var $a#2_1$5:Ref;
			var $a#3_1$5:Ref;
			var $t#0_1$5:Ref;
			var $t#1_1$5:Ref;
			var $t#2_1$5:Ref;
			var $t#3_1$5:Ref;
			var x_1$5:Ref;
			var xn_1$5:Ref;
			var xnn_1$5:Ref;
			var y_1$5:Ref;
			var yn_1$5:Ref;
			var ynn_1$5:Ref;
			var $h_1$5:Heap;

			// declare copies of parameters for allocation strategy
			var x$5:Ref;
			var y$5:Ref;
			// declare locals for strategy 6
			// locals for version _0
			var $a#0_0$6:Ref;
			var $a#1_0$6:Ref;
			var $a#2_0$6:Ref;
			var $a#3_0$6:Ref;
			var $t#0_0$6:Ref;
			var $t#1_0$6:Ref;
			var $t#2_0$6:Ref;
			var n_0$6:Ref;
			var x_0$6:Ref;
			var xn_0$6:Ref;
			var y_0$6:Ref;
			var yn_0$6:Ref;
			var $h_0$6:Heap;
			// locals for version _1
			var $a#0_1$6:Ref;
			var $a#1_1$6:Ref;
			var $a#2_1$6:Ref;
			var $a#3_1$6:Ref;
			var $t#0_1$6:Ref;
			var $t#1_1$6:Ref;
			var $t#2_1$6:Ref;
			var $t#3_1$6:Ref;
			var x_1$6:Ref;
			var xn_1$6:Ref;
			var xnn_1$6:Ref;
			var y_1$6:Ref;
			var yn_1$6:Ref;
			var ynn_1$6:Ref;
			var $h_1$6:Heap;

			// declare copies of parameters for allocation strategy
			var x$6:Ref;
			var y$6:Ref;
			// declare locals for strategy 7
			// locals for version _0
			var $a#0_0$7:Ref;
			var $a#1_0$7:Ref;
			var $a#2_0$7:Ref;
			var $a#3_0$7:Ref;
			var $t#0_0$7:Ref;
			var $t#1_0$7:Ref;
			var $t#2_0$7:Ref;
			var n_0$7:Ref;
			var x_0$7:Ref;
			var xn_0$7:Ref;
			var y_0$7:Ref;
			var yn_0$7:Ref;
			var $h_0$7:Heap;
			// locals for version _1
			var $a#0_1$7:Ref;
			var $a#1_1$7:Ref;
			var $a#2_1$7:Ref;
			var $a#3_1$7:Ref;
			var $t#0_1$7:Ref;
			var $t#1_1$7:Ref;
			var $t#2_1$7:Ref;
			var $t#3_1$7:Ref;
			var x_1$7:Ref;
			var xn_1$7:Ref;
			var xnn_1$7:Ref;
			var y_1$7:Ref;
			var yn_1$7:Ref;
			var ynn_1$7:Ref;
			var $h_1$7:Heap;

			// declare copies of parameters for allocation strategy
			var x$7:Ref;
			var y$7:Ref;
			// declare locals for strategy 8
			// locals for version _0
			var $a#0_0$8:Ref;
			var $a#1_0$8:Ref;
			var $a#2_0$8:Ref;
			var $a#3_0$8:Ref;
			var $t#0_0$8:Ref;
			var $t#1_0$8:Ref;
			var $t#2_0$8:Ref;
			var n_0$8:Ref;
			var x_0$8:Ref;
			var xn_0$8:Ref;
			var y_0$8:Ref;
			var yn_0$8:Ref;
			var $h_0$8:Heap;
			// locals for version _1
			var $a#0_1$8:Ref;
			var $a#1_1$8:Ref;
			var $a#2_1$8:Ref;
			var $a#3_1$8:Ref;
			var $t#0_1$8:Ref;
			var $t#1_1$8:Ref;
			var $t#2_1$8:Ref;
			var $t#3_1$8:Ref;
			var x_1$8:Ref;
			var xn_1$8:Ref;
			var xnn_1$8:Ref;
			var y_1$8:Ref;
			var yn_1$8:Ref;
			var ynn_1$8:Ref;
			var $h_1$8:Heap;

			// declare copies of parameters for allocation strategy
			var x$8:Ref;
			var y$8:Ref;
			// declare locals for strategy 9
			// locals for version _0
			var $a#0_0$9:Ref;
			var $a#1_0$9:Ref;
			var $a#2_0$9:Ref;
			var $a#3_0$9:Ref;
			var $t#0_0$9:Ref;
			var $t#1_0$9:Ref;
			var $t#2_0$9:Ref;
			var n_0$9:Ref;
			var x_0$9:Ref;
			var xn_0$9:Ref;
			var y_0$9:Ref;
			var yn_0$9:Ref;
			var $h_0$9:Heap;
			// locals for version _1
			var $a#0_1$9:Ref;
			var $a#1_1$9:Ref;
			var $a#2_1$9:Ref;
			var $a#3_1$9:Ref;
			var $t#0_1$9:Ref;
			var $t#1_1$9:Ref;
			var $t#2_1$9:Ref;
			var $t#3_1$9:Ref;
			var x_1$9:Ref;
			var xn_1$9:Ref;
			var xnn_1$9:Ref;
			var y_1$9:Ref;
			var yn_1$9:Ref;
			var ynn_1$9:Ref;
			var $h_1$9:Heap;

			// declare copies of parameters for allocation strategy
			var x$9:Ref;
			var y$9:Ref;
			// declare locals for strategy 10
			// locals for version _0
			var $a#0_0$10:Ref;
			var $a#1_0$10:Ref;
			var $a#2_0$10:Ref;
			var $a#3_0$10:Ref;
			var $t#0_0$10:Ref;
			var $t#1_0$10:Ref;
			var $t#2_0$10:Ref;
			var n_0$10:Ref;
			var x_0$10:Ref;
			var xn_0$10:Ref;
			var y_0$10:Ref;
			var yn_0$10:Ref;
			var $h_0$10:Heap;
			// locals for version _1
			var $a#0_1$10:Ref;
			var $a#1_1$10:Ref;
			var $a#2_1$10:Ref;
			var $a#3_1$10:Ref;
			var $t#0_1$10:Ref;
			var $t#1_1$10:Ref;
			var $t#2_1$10:Ref;
			var $t#3_1$10:Ref;
			var x_1$10:Ref;
			var xn_1$10:Ref;
			var xnn_1$10:Ref;
			var y_1$10:Ref;
			var yn_1$10:Ref;
			var ynn_1$10:Ref;
			var $h_1$10:Heap;

			// declare copies of parameters for allocation strategy
			var x$10:Ref;
			var y$10:Ref;
			// declare locals for strategy 11
			// locals for version _0
			var $a#0_0$11:Ref;
			var $a#1_0$11:Ref;
			var $a#2_0$11:Ref;
			var $a#3_0$11:Ref;
			var $t#0_0$11:Ref;
			var $t#1_0$11:Ref;
			var $t#2_0$11:Ref;
			var n_0$11:Ref;
			var x_0$11:Ref;
			var xn_0$11:Ref;
			var y_0$11:Ref;
			var yn_0$11:Ref;
			var $h_0$11:Heap;
			// locals for version _1
			var $a#0_1$11:Ref;
			var $a#1_1$11:Ref;
			var $a#2_1$11:Ref;
			var $a#3_1$11:Ref;
			var $t#0_1$11:Ref;
			var $t#1_1$11:Ref;
			var $t#2_1$11:Ref;
			var $t#3_1$11:Ref;
			var x_1$11:Ref;
			var xn_1$11:Ref;
			var xnn_1$11:Ref;
			var y_1$11:Ref;
			var yn_1$11:Ref;
			var ynn_1$11:Ref;
			var $h_1$11:Heap;

			// declare copies of parameters for allocation strategy
			var x$11:Ref;
			var y$11:Ref;
			// declare locals for strategy 12
			// locals for version _0
			var $a#0_0$12:Ref;
			var $a#1_0$12:Ref;
			var $a#2_0$12:Ref;
			var $a#3_0$12:Ref;
			var $t#0_0$12:Ref;
			var $t#1_0$12:Ref;
			var $t#2_0$12:Ref;
			var n_0$12:Ref;
			var x_0$12:Ref;
			var xn_0$12:Ref;
			var y_0$12:Ref;
			var yn_0$12:Ref;
			var $h_0$12:Heap;
			// locals for version _1
			var $a#0_1$12:Ref;
			var $a#1_1$12:Ref;
			var $a#2_1$12:Ref;
			var $a#3_1$12:Ref;
			var $t#0_1$12:Ref;
			var $t#1_1$12:Ref;
			var $t#2_1$12:Ref;
			var $t#3_1$12:Ref;
			var x_1$12:Ref;
			var xn_1$12:Ref;
			var xnn_1$12:Ref;
			var y_1$12:Ref;
			var yn_1$12:Ref;
			var ynn_1$12:Ref;
			var $h_1$12:Heap;

			// declare copies of parameters for allocation strategy
			var x$12:Ref;
			var y$12:Ref;
			// declare locals for strategy 13
			// locals for version _0
			var $a#0_0$13:Ref;
			var $a#1_0$13:Ref;
			var $a#2_0$13:Ref;
			var $a#3_0$13:Ref;
			var $t#0_0$13:Ref;
			var $t#1_0$13:Ref;
			var $t#2_0$13:Ref;
			var n_0$13:Ref;
			var x_0$13:Ref;
			var xn_0$13:Ref;
			var y_0$13:Ref;
			var yn_0$13:Ref;
			var $h_0$13:Heap;
			// locals for version _1
			var $a#0_1$13:Ref;
			var $a#1_1$13:Ref;
			var $a#2_1$13:Ref;
			var $a#3_1$13:Ref;
			var $t#0_1$13:Ref;
			var $t#1_1$13:Ref;
			var $t#2_1$13:Ref;
			var $t#3_1$13:Ref;
			var x_1$13:Ref;
			var xn_1$13:Ref;
			var xnn_1$13:Ref;
			var y_1$13:Ref;
			var yn_1$13:Ref;
			var ynn_1$13:Ref;
			var $h_1$13:Heap;

			// declare copies of parameters for allocation strategy
			var x$13:Ref;
			var y$13:Ref;
			// declare locals for strategy 14
			// locals for version _0
			var $a#0_0$14:Ref;
			var $a#1_0$14:Ref;
			var $a#2_0$14:Ref;
			var $a#3_0$14:Ref;
			var $t#0_0$14:Ref;
			var $t#1_0$14:Ref;
			var $t#2_0$14:Ref;
			var n_0$14:Ref;
			var x_0$14:Ref;
			var xn_0$14:Ref;
			var y_0$14:Ref;
			var yn_0$14:Ref;
			var $h_0$14:Heap;
			// locals for version _1
			var $a#0_1$14:Ref;
			var $a#1_1$14:Ref;
			var $a#2_1$14:Ref;
			var $a#3_1$14:Ref;
			var $t#0_1$14:Ref;
			var $t#1_1$14:Ref;
			var $t#2_1$14:Ref;
			var $t#3_1$14:Ref;
			var x_1$14:Ref;
			var xn_1$14:Ref;
			var xnn_1$14:Ref;
			var y_1$14:Ref;
			var yn_1$14:Ref;
			var ynn_1$14:Ref;
			var $h_1$14:Heap;

			// declare copies of parameters for allocation strategy
			var x$14:Ref;
			var y$14:Ref;
			// declare locals for strategy 15
			// locals for version _0
			var $a#0_0$15:Ref;
			var $a#1_0$15:Ref;
			var $a#2_0$15:Ref;
			var $a#3_0$15:Ref;
			var $t#0_0$15:Ref;
			var $t#1_0$15:Ref;
			var $t#2_0$15:Ref;
			var n_0$15:Ref;
			var x_0$15:Ref;
			var xn_0$15:Ref;
			var y_0$15:Ref;
			var yn_0$15:Ref;
			var $h_0$15:Heap;
			// locals for version _1
			var $a#0_1$15:Ref;
			var $a#1_1$15:Ref;
			var $a#2_1$15:Ref;
			var $a#3_1$15:Ref;
			var $t#0_1$15:Ref;
			var $t#1_1$15:Ref;
			var $t#2_1$15:Ref;
			var $t#3_1$15:Ref;
			var x_1$15:Ref;
			var xn_1$15:Ref;
			var xnn_1$15:Ref;
			var y_1$15:Ref;
			var yn_1$15:Ref;
			var ynn_1$15:Ref;
			var $h_1$15:Heap;

			// declare copies of parameters for allocation strategy
			var x$15:Ref;
			var y$15:Ref;
			// declare locals for strategy 16
			// locals for version _0
			var $a#0_0$16:Ref;
			var $a#1_0$16:Ref;
			var $a#2_0$16:Ref;
			var $a#3_0$16:Ref;
			var $t#0_0$16:Ref;
			var $t#1_0$16:Ref;
			var $t#2_0$16:Ref;
			var n_0$16:Ref;
			var x_0$16:Ref;
			var xn_0$16:Ref;
			var y_0$16:Ref;
			var yn_0$16:Ref;
			var $h_0$16:Heap;
			// locals for version _1
			var $a#0_1$16:Ref;
			var $a#1_1$16:Ref;
			var $a#2_1$16:Ref;
			var $a#3_1$16:Ref;
			var $t#0_1$16:Ref;
			var $t#1_1$16:Ref;
			var $t#2_1$16:Ref;
			var $t#3_1$16:Ref;
			var x_1$16:Ref;
			var xn_1$16:Ref;
			var xnn_1$16:Ref;
			var y_1$16:Ref;
			var yn_1$16:Ref;
			var ynn_1$16:Ref;
			var $h_1$16:Heap;

			// declare copies of parameters for allocation strategy
			var x$16:Ref;
			var y$16:Ref;
			// declare locals for strategy 17
			// locals for version _0
			var $a#0_0$17:Ref;
			var $a#1_0$17:Ref;
			var $a#2_0$17:Ref;
			var $a#3_0$17:Ref;
			var $t#0_0$17:Ref;
			var $t#1_0$17:Ref;
			var $t#2_0$17:Ref;
			var n_0$17:Ref;
			var x_0$17:Ref;
			var xn_0$17:Ref;
			var y_0$17:Ref;
			var yn_0$17:Ref;
			var $h_0$17:Heap;
			// locals for version _1
			var $a#0_1$17:Ref;
			var $a#1_1$17:Ref;
			var $a#2_1$17:Ref;
			var $a#3_1$17:Ref;
			var $t#0_1$17:Ref;
			var $t#1_1$17:Ref;
			var $t#2_1$17:Ref;
			var $t#3_1$17:Ref;
			var x_1$17:Ref;
			var xn_1$17:Ref;
			var xnn_1$17:Ref;
			var y_1$17:Ref;
			var yn_1$17:Ref;
			var ynn_1$17:Ref;
			var $h_1$17:Heap;

			// declare copies of parameters for allocation strategy
			var x$17:Ref;
			var y$17:Ref;
			// declare locals for strategy 18
			// locals for version _0
			var $a#0_0$18:Ref;
			var $a#1_0$18:Ref;
			var $a#2_0$18:Ref;
			var $a#3_0$18:Ref;
			var $t#0_0$18:Ref;
			var $t#1_0$18:Ref;
			var $t#2_0$18:Ref;
			var n_0$18:Ref;
			var x_0$18:Ref;
			var xn_0$18:Ref;
			var y_0$18:Ref;
			var yn_0$18:Ref;
			var $h_0$18:Heap;
			// locals for version _1
			var $a#0_1$18:Ref;
			var $a#1_1$18:Ref;
			var $a#2_1$18:Ref;
			var $a#3_1$18:Ref;
			var $t#0_1$18:Ref;
			var $t#1_1$18:Ref;
			var $t#2_1$18:Ref;
			var $t#3_1$18:Ref;
			var x_1$18:Ref;
			var xn_1$18:Ref;
			var xnn_1$18:Ref;
			var y_1$18:Ref;
			var yn_1$18:Ref;
			var ynn_1$18:Ref;
			var $h_1$18:Heap;

			// declare copies of parameters for allocation strategy
			var x$18:Ref;
			var y$18:Ref;
			// declare locals for strategy 19
			// locals for version _0
			var $a#0_0$19:Ref;
			var $a#1_0$19:Ref;
			var $a#2_0$19:Ref;
			var $a#3_0$19:Ref;
			var $t#0_0$19:Ref;
			var $t#1_0$19:Ref;
			var $t#2_0$19:Ref;
			var n_0$19:Ref;
			var x_0$19:Ref;
			var xn_0$19:Ref;
			var y_0$19:Ref;
			var yn_0$19:Ref;
			var $h_0$19:Heap;
			// locals for version _1
			var $a#0_1$19:Ref;
			var $a#1_1$19:Ref;
			var $a#2_1$19:Ref;
			var $a#3_1$19:Ref;
			var $t#0_1$19:Ref;
			var $t#1_1$19:Ref;
			var $t#2_1$19:Ref;
			var $t#3_1$19:Ref;
			var x_1$19:Ref;
			var xn_1$19:Ref;
			var xnn_1$19:Ref;
			var y_1$19:Ref;
			var yn_1$19:Ref;
			var ynn_1$19:Ref;
			var $h_1$19:Heap;

			// declare copies of parameters for allocation strategy
			var x$19:Ref;
			var y$19:Ref;
			// declare locals for strategy 20
			// locals for version _0
			var $a#0_0$20:Ref;
			var $a#1_0$20:Ref;
			var $a#2_0$20:Ref;
			var $a#3_0$20:Ref;
			var $t#0_0$20:Ref;
			var $t#1_0$20:Ref;
			var $t#2_0$20:Ref;
			var n_0$20:Ref;
			var x_0$20:Ref;
			var xn_0$20:Ref;
			var y_0$20:Ref;
			var yn_0$20:Ref;
			var $h_0$20:Heap;
			// locals for version _1
			var $a#0_1$20:Ref;
			var $a#1_1$20:Ref;
			var $a#2_1$20:Ref;
			var $a#3_1$20:Ref;
			var $t#0_1$20:Ref;
			var $t#1_1$20:Ref;
			var $t#2_1$20:Ref;
			var $t#3_1$20:Ref;
			var x_1$20:Ref;
			var xn_1$20:Ref;
			var xnn_1$20:Ref;
			var y_1$20:Ref;
			var yn_1$20:Ref;
			var ynn_1$20:Ref;
			var $h_1$20:Heap;

			// declare copies of parameters for allocation strategy
			var x$20:Ref;
			var y$20:Ref;
			// declare locals for strategy 21
			// locals for version _0
			var $a#0_0$21:Ref;
			var $a#1_0$21:Ref;
			var $a#2_0$21:Ref;
			var $a#3_0$21:Ref;
			var $t#0_0$21:Ref;
			var $t#1_0$21:Ref;
			var $t#2_0$21:Ref;
			var n_0$21:Ref;
			var x_0$21:Ref;
			var xn_0$21:Ref;
			var y_0$21:Ref;
			var yn_0$21:Ref;
			var $h_0$21:Heap;
			// locals for version _1
			var $a#0_1$21:Ref;
			var $a#1_1$21:Ref;
			var $a#2_1$21:Ref;
			var $a#3_1$21:Ref;
			var $t#0_1$21:Ref;
			var $t#1_1$21:Ref;
			var $t#2_1$21:Ref;
			var $t#3_1$21:Ref;
			var x_1$21:Ref;
			var xn_1$21:Ref;
			var xnn_1$21:Ref;
			var y_1$21:Ref;
			var yn_1$21:Ref;
			var ynn_1$21:Ref;
			var $h_1$21:Heap;

			// declare copies of parameters for allocation strategy
			var x$21:Ref;
			var y$21:Ref;
			// declare locals for strategy 22
			// locals for version _0
			var $a#0_0$22:Ref;
			var $a#1_0$22:Ref;
			var $a#2_0$22:Ref;
			var $a#3_0$22:Ref;
			var $t#0_0$22:Ref;
			var $t#1_0$22:Ref;
			var $t#2_0$22:Ref;
			var n_0$22:Ref;
			var x_0$22:Ref;
			var xn_0$22:Ref;
			var y_0$22:Ref;
			var yn_0$22:Ref;
			var $h_0$22:Heap;
			// locals for version _1
			var $a#0_1$22:Ref;
			var $a#1_1$22:Ref;
			var $a#2_1$22:Ref;
			var $a#3_1$22:Ref;
			var $t#0_1$22:Ref;
			var $t#1_1$22:Ref;
			var $t#2_1$22:Ref;
			var $t#3_1$22:Ref;
			var x_1$22:Ref;
			var xn_1$22:Ref;
			var xnn_1$22:Ref;
			var y_1$22:Ref;
			var yn_1$22:Ref;
			var ynn_1$22:Ref;
			var $h_1$22:Heap;

			// declare copies of parameters for allocation strategy
			var x$22:Ref;
			var y$22:Ref;
			// declare locals for strategy 23
			// locals for version _0
			var $a#0_0$23:Ref;
			var $a#1_0$23:Ref;
			var $a#2_0$23:Ref;
			var $a#3_0$23:Ref;
			var $t#0_0$23:Ref;
			var $t#1_0$23:Ref;
			var $t#2_0$23:Ref;
			var n_0$23:Ref;
			var x_0$23:Ref;
			var xn_0$23:Ref;
			var y_0$23:Ref;
			var yn_0$23:Ref;
			var $h_0$23:Heap;
			// locals for version _1
			var $a#0_1$23:Ref;
			var $a#1_1$23:Ref;
			var $a#2_1$23:Ref;
			var $a#3_1$23:Ref;
			var $t#0_1$23:Ref;
			var $t#1_1$23:Ref;
			var $t#2_1$23:Ref;
			var $t#3_1$23:Ref;
			var x_1$23:Ref;
			var xn_1$23:Ref;
			var xnn_1$23:Ref;
			var y_1$23:Ref;
			var yn_1$23:Ref;
			var ynn_1$23:Ref;
			var $h_1$23:Heap;

			// declare copies of parameters for allocation strategy
			var x$23:Ref;
			var y$23:Ref;


			// initialise locals for strategy 0	

			// initialise locals for version _0
			$a#0_0$0 := $Null;
			$a#1_0$0 := $Null;
			$a#2_0$0 := $Null;
			$a#3_0$0 := $Null;
			$t#0_0$0 := $Null;
			$t#1_0$0 := $Null;
			$t#2_0$0 := $Null;
			n_0$0 := $Null;
			x_0$0 := $Null;
			xn_0$0 := $Null;
			y_0$0 := $Null;
			yn_0$0 := $Null;

			// initialise locals for version _1
			$a#0_1$0 := $Null;
			$a#1_1$0 := $Null;
			$a#2_1$0 := $Null;
			$a#3_1$0 := $Null;
			$t#0_1$0 := $Null;
			$t#1_1$0 := $Null;
			$t#2_1$0 := $Null;
			$t#3_1$0 := $Null;
			x_1$0 := $Null;
			xn_1$0 := $Null;
			xnn_1$0 := $Null;
			y_1$0 := $Null;
			yn_1$0 := $Null;
			ynn_1$0 := $Null;
			// initialise locals for strategy 1	

			// initialise locals for version _0
			$a#0_0$1 := $Null;
			$a#1_0$1 := $Null;
			$a#2_0$1 := $Null;
			$a#3_0$1 := $Null;
			$t#0_0$1 := $Null;
			$t#1_0$1 := $Null;
			$t#2_0$1 := $Null;
			n_0$1 := $Null;
			x_0$1 := $Null;
			xn_0$1 := $Null;
			y_0$1 := $Null;
			yn_0$1 := $Null;

			// initialise locals for version _1
			$a#0_1$1 := $Null;
			$a#1_1$1 := $Null;
			$a#2_1$1 := $Null;
			$a#3_1$1 := $Null;
			$t#0_1$1 := $Null;
			$t#1_1$1 := $Null;
			$t#2_1$1 := $Null;
			$t#3_1$1 := $Null;
			x_1$1 := $Null;
			xn_1$1 := $Null;
			xnn_1$1 := $Null;
			y_1$1 := $Null;
			yn_1$1 := $Null;
			ynn_1$1 := $Null;
			// initialise locals for strategy 2	

			// initialise locals for version _0
			$a#0_0$2 := $Null;
			$a#1_0$2 := $Null;
			$a#2_0$2 := $Null;
			$a#3_0$2 := $Null;
			$t#0_0$2 := $Null;
			$t#1_0$2 := $Null;
			$t#2_0$2 := $Null;
			n_0$2 := $Null;
			x_0$2 := $Null;
			xn_0$2 := $Null;
			y_0$2 := $Null;
			yn_0$2 := $Null;

			// initialise locals for version _1
			$a#0_1$2 := $Null;
			$a#1_1$2 := $Null;
			$a#2_1$2 := $Null;
			$a#3_1$2 := $Null;
			$t#0_1$2 := $Null;
			$t#1_1$2 := $Null;
			$t#2_1$2 := $Null;
			$t#3_1$2 := $Null;
			x_1$2 := $Null;
			xn_1$2 := $Null;
			xnn_1$2 := $Null;
			y_1$2 := $Null;
			yn_1$2 := $Null;
			ynn_1$2 := $Null;
			// initialise locals for strategy 3	

			// initialise locals for version _0
			$a#0_0$3 := $Null;
			$a#1_0$3 := $Null;
			$a#2_0$3 := $Null;
			$a#3_0$3 := $Null;
			$t#0_0$3 := $Null;
			$t#1_0$3 := $Null;
			$t#2_0$3 := $Null;
			n_0$3 := $Null;
			x_0$3 := $Null;
			xn_0$3 := $Null;
			y_0$3 := $Null;
			yn_0$3 := $Null;

			// initialise locals for version _1
			$a#0_1$3 := $Null;
			$a#1_1$3 := $Null;
			$a#2_1$3 := $Null;
			$a#3_1$3 := $Null;
			$t#0_1$3 := $Null;
			$t#1_1$3 := $Null;
			$t#2_1$3 := $Null;
			$t#3_1$3 := $Null;
			x_1$3 := $Null;
			xn_1$3 := $Null;
			xnn_1$3 := $Null;
			y_1$3 := $Null;
			yn_1$3 := $Null;
			ynn_1$3 := $Null;
			// initialise locals for strategy 4	

			// initialise locals for version _0
			$a#0_0$4 := $Null;
			$a#1_0$4 := $Null;
			$a#2_0$4 := $Null;
			$a#3_0$4 := $Null;
			$t#0_0$4 := $Null;
			$t#1_0$4 := $Null;
			$t#2_0$4 := $Null;
			n_0$4 := $Null;
			x_0$4 := $Null;
			xn_0$4 := $Null;
			y_0$4 := $Null;
			yn_0$4 := $Null;

			// initialise locals for version _1
			$a#0_1$4 := $Null;
			$a#1_1$4 := $Null;
			$a#2_1$4 := $Null;
			$a#3_1$4 := $Null;
			$t#0_1$4 := $Null;
			$t#1_1$4 := $Null;
			$t#2_1$4 := $Null;
			$t#3_1$4 := $Null;
			x_1$4 := $Null;
			xn_1$4 := $Null;
			xnn_1$4 := $Null;
			y_1$4 := $Null;
			yn_1$4 := $Null;
			ynn_1$4 := $Null;
			// initialise locals for strategy 5	

			// initialise locals for version _0
			$a#0_0$5 := $Null;
			$a#1_0$5 := $Null;
			$a#2_0$5 := $Null;
			$a#3_0$5 := $Null;
			$t#0_0$5 := $Null;
			$t#1_0$5 := $Null;
			$t#2_0$5 := $Null;
			n_0$5 := $Null;
			x_0$5 := $Null;
			xn_0$5 := $Null;
			y_0$5 := $Null;
			yn_0$5 := $Null;

			// initialise locals for version _1
			$a#0_1$5 := $Null;
			$a#1_1$5 := $Null;
			$a#2_1$5 := $Null;
			$a#3_1$5 := $Null;
			$t#0_1$5 := $Null;
			$t#1_1$5 := $Null;
			$t#2_1$5 := $Null;
			$t#3_1$5 := $Null;
			x_1$5 := $Null;
			xn_1$5 := $Null;
			xnn_1$5 := $Null;
			y_1$5 := $Null;
			yn_1$5 := $Null;
			ynn_1$5 := $Null;
			// initialise locals for strategy 6	

			// initialise locals for version _0
			$a#0_0$6 := $Null;
			$a#1_0$6 := $Null;
			$a#2_0$6 := $Null;
			$a#3_0$6 := $Null;
			$t#0_0$6 := $Null;
			$t#1_0$6 := $Null;
			$t#2_0$6 := $Null;
			n_0$6 := $Null;
			x_0$6 := $Null;
			xn_0$6 := $Null;
			y_0$6 := $Null;
			yn_0$6 := $Null;

			// initialise locals for version _1
			$a#0_1$6 := $Null;
			$a#1_1$6 := $Null;
			$a#2_1$6 := $Null;
			$a#3_1$6 := $Null;
			$t#0_1$6 := $Null;
			$t#1_1$6 := $Null;
			$t#2_1$6 := $Null;
			$t#3_1$6 := $Null;
			x_1$6 := $Null;
			xn_1$6 := $Null;
			xnn_1$6 := $Null;
			y_1$6 := $Null;
			yn_1$6 := $Null;
			ynn_1$6 := $Null;
			// initialise locals for strategy 7	

			// initialise locals for version _0
			$a#0_0$7 := $Null;
			$a#1_0$7 := $Null;
			$a#2_0$7 := $Null;
			$a#3_0$7 := $Null;
			$t#0_0$7 := $Null;
			$t#1_0$7 := $Null;
			$t#2_0$7 := $Null;
			n_0$7 := $Null;
			x_0$7 := $Null;
			xn_0$7 := $Null;
			y_0$7 := $Null;
			yn_0$7 := $Null;

			// initialise locals for version _1
			$a#0_1$7 := $Null;
			$a#1_1$7 := $Null;
			$a#2_1$7 := $Null;
			$a#3_1$7 := $Null;
			$t#0_1$7 := $Null;
			$t#1_1$7 := $Null;
			$t#2_1$7 := $Null;
			$t#3_1$7 := $Null;
			x_1$7 := $Null;
			xn_1$7 := $Null;
			xnn_1$7 := $Null;
			y_1$7 := $Null;
			yn_1$7 := $Null;
			ynn_1$7 := $Null;
			// initialise locals for strategy 8	

			// initialise locals for version _0
			$a#0_0$8 := $Null;
			$a#1_0$8 := $Null;
			$a#2_0$8 := $Null;
			$a#3_0$8 := $Null;
			$t#0_0$8 := $Null;
			$t#1_0$8 := $Null;
			$t#2_0$8 := $Null;
			n_0$8 := $Null;
			x_0$8 := $Null;
			xn_0$8 := $Null;
			y_0$8 := $Null;
			yn_0$8 := $Null;

			// initialise locals for version _1
			$a#0_1$8 := $Null;
			$a#1_1$8 := $Null;
			$a#2_1$8 := $Null;
			$a#3_1$8 := $Null;
			$t#0_1$8 := $Null;
			$t#1_1$8 := $Null;
			$t#2_1$8 := $Null;
			$t#3_1$8 := $Null;
			x_1$8 := $Null;
			xn_1$8 := $Null;
			xnn_1$8 := $Null;
			y_1$8 := $Null;
			yn_1$8 := $Null;
			ynn_1$8 := $Null;
			// initialise locals for strategy 9	

			// initialise locals for version _0
			$a#0_0$9 := $Null;
			$a#1_0$9 := $Null;
			$a#2_0$9 := $Null;
			$a#3_0$9 := $Null;
			$t#0_0$9 := $Null;
			$t#1_0$9 := $Null;
			$t#2_0$9 := $Null;
			n_0$9 := $Null;
			x_0$9 := $Null;
			xn_0$9 := $Null;
			y_0$9 := $Null;
			yn_0$9 := $Null;

			// initialise locals for version _1
			$a#0_1$9 := $Null;
			$a#1_1$9 := $Null;
			$a#2_1$9 := $Null;
			$a#3_1$9 := $Null;
			$t#0_1$9 := $Null;
			$t#1_1$9 := $Null;
			$t#2_1$9 := $Null;
			$t#3_1$9 := $Null;
			x_1$9 := $Null;
			xn_1$9 := $Null;
			xnn_1$9 := $Null;
			y_1$9 := $Null;
			yn_1$9 := $Null;
			ynn_1$9 := $Null;
			// initialise locals for strategy 10	

			// initialise locals for version _0
			$a#0_0$10 := $Null;
			$a#1_0$10 := $Null;
			$a#2_0$10 := $Null;
			$a#3_0$10 := $Null;
			$t#0_0$10 := $Null;
			$t#1_0$10 := $Null;
			$t#2_0$10 := $Null;
			n_0$10 := $Null;
			x_0$10 := $Null;
			xn_0$10 := $Null;
			y_0$10 := $Null;
			yn_0$10 := $Null;

			// initialise locals for version _1
			$a#0_1$10 := $Null;
			$a#1_1$10 := $Null;
			$a#2_1$10 := $Null;
			$a#3_1$10 := $Null;
			$t#0_1$10 := $Null;
			$t#1_1$10 := $Null;
			$t#2_1$10 := $Null;
			$t#3_1$10 := $Null;
			x_1$10 := $Null;
			xn_1$10 := $Null;
			xnn_1$10 := $Null;
			y_1$10 := $Null;
			yn_1$10 := $Null;
			ynn_1$10 := $Null;
			// initialise locals for strategy 11	

			// initialise locals for version _0
			$a#0_0$11 := $Null;
			$a#1_0$11 := $Null;
			$a#2_0$11 := $Null;
			$a#3_0$11 := $Null;
			$t#0_0$11 := $Null;
			$t#1_0$11 := $Null;
			$t#2_0$11 := $Null;
			n_0$11 := $Null;
			x_0$11 := $Null;
			xn_0$11 := $Null;
			y_0$11 := $Null;
			yn_0$11 := $Null;

			// initialise locals for version _1
			$a#0_1$11 := $Null;
			$a#1_1$11 := $Null;
			$a#2_1$11 := $Null;
			$a#3_1$11 := $Null;
			$t#0_1$11 := $Null;
			$t#1_1$11 := $Null;
			$t#2_1$11 := $Null;
			$t#3_1$11 := $Null;
			x_1$11 := $Null;
			xn_1$11 := $Null;
			xnn_1$11 := $Null;
			y_1$11 := $Null;
			yn_1$11 := $Null;
			ynn_1$11 := $Null;
			// initialise locals for strategy 12	

			// initialise locals for version _0
			$a#0_0$12 := $Null;
			$a#1_0$12 := $Null;
			$a#2_0$12 := $Null;
			$a#3_0$12 := $Null;
			$t#0_0$12 := $Null;
			$t#1_0$12 := $Null;
			$t#2_0$12 := $Null;
			n_0$12 := $Null;
			x_0$12 := $Null;
			xn_0$12 := $Null;
			y_0$12 := $Null;
			yn_0$12 := $Null;

			// initialise locals for version _1
			$a#0_1$12 := $Null;
			$a#1_1$12 := $Null;
			$a#2_1$12 := $Null;
			$a#3_1$12 := $Null;
			$t#0_1$12 := $Null;
			$t#1_1$12 := $Null;
			$t#2_1$12 := $Null;
			$t#3_1$12 := $Null;
			x_1$12 := $Null;
			xn_1$12 := $Null;
			xnn_1$12 := $Null;
			y_1$12 := $Null;
			yn_1$12 := $Null;
			ynn_1$12 := $Null;
			// initialise locals for strategy 13	

			// initialise locals for version _0
			$a#0_0$13 := $Null;
			$a#1_0$13 := $Null;
			$a#2_0$13 := $Null;
			$a#3_0$13 := $Null;
			$t#0_0$13 := $Null;
			$t#1_0$13 := $Null;
			$t#2_0$13 := $Null;
			n_0$13 := $Null;
			x_0$13 := $Null;
			xn_0$13 := $Null;
			y_0$13 := $Null;
			yn_0$13 := $Null;

			// initialise locals for version _1
			$a#0_1$13 := $Null;
			$a#1_1$13 := $Null;
			$a#2_1$13 := $Null;
			$a#3_1$13 := $Null;
			$t#0_1$13 := $Null;
			$t#1_1$13 := $Null;
			$t#2_1$13 := $Null;
			$t#3_1$13 := $Null;
			x_1$13 := $Null;
			xn_1$13 := $Null;
			xnn_1$13 := $Null;
			y_1$13 := $Null;
			yn_1$13 := $Null;
			ynn_1$13 := $Null;
			// initialise locals for strategy 14	

			// initialise locals for version _0
			$a#0_0$14 := $Null;
			$a#1_0$14 := $Null;
			$a#2_0$14 := $Null;
			$a#3_0$14 := $Null;
			$t#0_0$14 := $Null;
			$t#1_0$14 := $Null;
			$t#2_0$14 := $Null;
			n_0$14 := $Null;
			x_0$14 := $Null;
			xn_0$14 := $Null;
			y_0$14 := $Null;
			yn_0$14 := $Null;

			// initialise locals for version _1
			$a#0_1$14 := $Null;
			$a#1_1$14 := $Null;
			$a#2_1$14 := $Null;
			$a#3_1$14 := $Null;
			$t#0_1$14 := $Null;
			$t#1_1$14 := $Null;
			$t#2_1$14 := $Null;
			$t#3_1$14 := $Null;
			x_1$14 := $Null;
			xn_1$14 := $Null;
			xnn_1$14 := $Null;
			y_1$14 := $Null;
			yn_1$14 := $Null;
			ynn_1$14 := $Null;
			// initialise locals for strategy 15	

			// initialise locals for version _0
			$a#0_0$15 := $Null;
			$a#1_0$15 := $Null;
			$a#2_0$15 := $Null;
			$a#3_0$15 := $Null;
			$t#0_0$15 := $Null;
			$t#1_0$15 := $Null;
			$t#2_0$15 := $Null;
			n_0$15 := $Null;
			x_0$15 := $Null;
			xn_0$15 := $Null;
			y_0$15 := $Null;
			yn_0$15 := $Null;

			// initialise locals for version _1
			$a#0_1$15 := $Null;
			$a#1_1$15 := $Null;
			$a#2_1$15 := $Null;
			$a#3_1$15 := $Null;
			$t#0_1$15 := $Null;
			$t#1_1$15 := $Null;
			$t#2_1$15 := $Null;
			$t#3_1$15 := $Null;
			x_1$15 := $Null;
			xn_1$15 := $Null;
			xnn_1$15 := $Null;
			y_1$15 := $Null;
			yn_1$15 := $Null;
			ynn_1$15 := $Null;
			// initialise locals for strategy 16	

			// initialise locals for version _0
			$a#0_0$16 := $Null;
			$a#1_0$16 := $Null;
			$a#2_0$16 := $Null;
			$a#3_0$16 := $Null;
			$t#0_0$16 := $Null;
			$t#1_0$16 := $Null;
			$t#2_0$16 := $Null;
			n_0$16 := $Null;
			x_0$16 := $Null;
			xn_0$16 := $Null;
			y_0$16 := $Null;
			yn_0$16 := $Null;

			// initialise locals for version _1
			$a#0_1$16 := $Null;
			$a#1_1$16 := $Null;
			$a#2_1$16 := $Null;
			$a#3_1$16 := $Null;
			$t#0_1$16 := $Null;
			$t#1_1$16 := $Null;
			$t#2_1$16 := $Null;
			$t#3_1$16 := $Null;
			x_1$16 := $Null;
			xn_1$16 := $Null;
			xnn_1$16 := $Null;
			y_1$16 := $Null;
			yn_1$16 := $Null;
			ynn_1$16 := $Null;
			// initialise locals for strategy 17	

			// initialise locals for version _0
			$a#0_0$17 := $Null;
			$a#1_0$17 := $Null;
			$a#2_0$17 := $Null;
			$a#3_0$17 := $Null;
			$t#0_0$17 := $Null;
			$t#1_0$17 := $Null;
			$t#2_0$17 := $Null;
			n_0$17 := $Null;
			x_0$17 := $Null;
			xn_0$17 := $Null;
			y_0$17 := $Null;
			yn_0$17 := $Null;

			// initialise locals for version _1
			$a#0_1$17 := $Null;
			$a#1_1$17 := $Null;
			$a#2_1$17 := $Null;
			$a#3_1$17 := $Null;
			$t#0_1$17 := $Null;
			$t#1_1$17 := $Null;
			$t#2_1$17 := $Null;
			$t#3_1$17 := $Null;
			x_1$17 := $Null;
			xn_1$17 := $Null;
			xnn_1$17 := $Null;
			y_1$17 := $Null;
			yn_1$17 := $Null;
			ynn_1$17 := $Null;
			// initialise locals for strategy 18	

			// initialise locals for version _0
			$a#0_0$18 := $Null;
			$a#1_0$18 := $Null;
			$a#2_0$18 := $Null;
			$a#3_0$18 := $Null;
			$t#0_0$18 := $Null;
			$t#1_0$18 := $Null;
			$t#2_0$18 := $Null;
			n_0$18 := $Null;
			x_0$18 := $Null;
			xn_0$18 := $Null;
			y_0$18 := $Null;
			yn_0$18 := $Null;

			// initialise locals for version _1
			$a#0_1$18 := $Null;
			$a#1_1$18 := $Null;
			$a#2_1$18 := $Null;
			$a#3_1$18 := $Null;
			$t#0_1$18 := $Null;
			$t#1_1$18 := $Null;
			$t#2_1$18 := $Null;
			$t#3_1$18 := $Null;
			x_1$18 := $Null;
			xn_1$18 := $Null;
			xnn_1$18 := $Null;
			y_1$18 := $Null;
			yn_1$18 := $Null;
			ynn_1$18 := $Null;
			// initialise locals for strategy 19	

			// initialise locals for version _0
			$a#0_0$19 := $Null;
			$a#1_0$19 := $Null;
			$a#2_0$19 := $Null;
			$a#3_0$19 := $Null;
			$t#0_0$19 := $Null;
			$t#1_0$19 := $Null;
			$t#2_0$19 := $Null;
			n_0$19 := $Null;
			x_0$19 := $Null;
			xn_0$19 := $Null;
			y_0$19 := $Null;
			yn_0$19 := $Null;

			// initialise locals for version _1
			$a#0_1$19 := $Null;
			$a#1_1$19 := $Null;
			$a#2_1$19 := $Null;
			$a#3_1$19 := $Null;
			$t#0_1$19 := $Null;
			$t#1_1$19 := $Null;
			$t#2_1$19 := $Null;
			$t#3_1$19 := $Null;
			x_1$19 := $Null;
			xn_1$19 := $Null;
			xnn_1$19 := $Null;
			y_1$19 := $Null;
			yn_1$19 := $Null;
			ynn_1$19 := $Null;
			// initialise locals for strategy 20	

			// initialise locals for version _0
			$a#0_0$20 := $Null;
			$a#1_0$20 := $Null;
			$a#2_0$20 := $Null;
			$a#3_0$20 := $Null;
			$t#0_0$20 := $Null;
			$t#1_0$20 := $Null;
			$t#2_0$20 := $Null;
			n_0$20 := $Null;
			x_0$20 := $Null;
			xn_0$20 := $Null;
			y_0$20 := $Null;
			yn_0$20 := $Null;

			// initialise locals for version _1
			$a#0_1$20 := $Null;
			$a#1_1$20 := $Null;
			$a#2_1$20 := $Null;
			$a#3_1$20 := $Null;
			$t#0_1$20 := $Null;
			$t#1_1$20 := $Null;
			$t#2_1$20 := $Null;
			$t#3_1$20 := $Null;
			x_1$20 := $Null;
			xn_1$20 := $Null;
			xnn_1$20 := $Null;
			y_1$20 := $Null;
			yn_1$20 := $Null;
			ynn_1$20 := $Null;
			// initialise locals for strategy 21	

			// initialise locals for version _0
			$a#0_0$21 := $Null;
			$a#1_0$21 := $Null;
			$a#2_0$21 := $Null;
			$a#3_0$21 := $Null;
			$t#0_0$21 := $Null;
			$t#1_0$21 := $Null;
			$t#2_0$21 := $Null;
			n_0$21 := $Null;
			x_0$21 := $Null;
			xn_0$21 := $Null;
			y_0$21 := $Null;
			yn_0$21 := $Null;

			// initialise locals for version _1
			$a#0_1$21 := $Null;
			$a#1_1$21 := $Null;
			$a#2_1$21 := $Null;
			$a#3_1$21 := $Null;
			$t#0_1$21 := $Null;
			$t#1_1$21 := $Null;
			$t#2_1$21 := $Null;
			$t#3_1$21 := $Null;
			x_1$21 := $Null;
			xn_1$21 := $Null;
			xnn_1$21 := $Null;
			y_1$21 := $Null;
			yn_1$21 := $Null;
			ynn_1$21 := $Null;
			// initialise locals for strategy 22	

			// initialise locals for version _0
			$a#0_0$22 := $Null;
			$a#1_0$22 := $Null;
			$a#2_0$22 := $Null;
			$a#3_0$22 := $Null;
			$t#0_0$22 := $Null;
			$t#1_0$22 := $Null;
			$t#2_0$22 := $Null;
			n_0$22 := $Null;
			x_0$22 := $Null;
			xn_0$22 := $Null;
			y_0$22 := $Null;
			yn_0$22 := $Null;

			// initialise locals for version _1
			$a#0_1$22 := $Null;
			$a#1_1$22 := $Null;
			$a#2_1$22 := $Null;
			$a#3_1$22 := $Null;
			$t#0_1$22 := $Null;
			$t#1_1$22 := $Null;
			$t#2_1$22 := $Null;
			$t#3_1$22 := $Null;
			x_1$22 := $Null;
			xn_1$22 := $Null;
			xnn_1$22 := $Null;
			y_1$22 := $Null;
			yn_1$22 := $Null;
			ynn_1$22 := $Null;
			// initialise locals for strategy 23	

			// initialise locals for version _0
			$a#0_0$23 := $Null;
			$a#1_0$23 := $Null;
			$a#2_0$23 := $Null;
			$a#3_0$23 := $Null;
			$t#0_0$23 := $Null;
			$t#1_0$23 := $Null;
			$t#2_0$23 := $Null;
			n_0$23 := $Null;
			x_0$23 := $Null;
			xn_0$23 := $Null;
			y_0$23 := $Null;
			yn_0$23 := $Null;

			// initialise locals for version _1
			$a#0_1$23 := $Null;
			$a#1_1$23 := $Null;
			$a#2_1$23 := $Null;
			$a#3_1$23 := $Null;
			$t#0_1$23 := $Null;
			$t#1_1$23 := $Null;
			$t#2_1$23 := $Null;
			$t#3_1$23 := $Null;
			x_1$23 := $Null;
			xn_1$23 := $Null;
			xnn_1$23 := $Null;
			y_1$23 := $Null;
			yn_1$23 := $Null;
			ynn_1$23 := $Null;


    assume $ReadObject($h,x);
    assume $ReadObject($h,y);


		    // restore heaps
		    $h_0$0 := $h;
		    $h_1$0 := $h;

		    x$0 := x;
		    y$0 := y;

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
			havoc $a#2_0$0; assume !$Allocated($h_0$0,$a#2_0$0);
			$h_0$0:=$Allocate($h_0$0,$a#2_0$0); assume $GoodHeap($h_0$0);
			assume $AllocatedObject($h_0$0, $a#2_0$0);
			assert $FieldsNull($h_0$0, $a#2_0$0);
			assert $ReachNull($h_0$0, $a#2_0$0);
			havoc $a#3_0$0; assume !$Allocated($h_0$0,$a#3_0$0);
			$h_0$0:=$Allocate($h_0$0,$a#3_0$0); assume $GoodHeap($h_0$0);
			assume $AllocatedObject($h_0$0, $a#3_0$0);
			assert $FieldsNull($h_0$0, $a#3_0$0);
			assert $ReachNull($h_0$0, $a#3_0$0);
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
			havoc $a#2_1$0; assume !$Allocated($h_1$0,$a#2_1$0);
			$h_1$0:=$Allocate($h_1$0,$a#2_1$0); assume $GoodHeap($h_1$0);
			assume $AllocatedObject($h_1$0, $a#2_1$0);
			assert $FieldsNull($h_1$0, $a#2_1$0);
			assert $ReachNull($h_1$0, $a#2_1$0);
			havoc $a#3_1$0; assume !$Allocated($h_1$0,$a#3_1$0);
			$h_1$0:=$Allocate($h_1$0,$a#3_1$0); assume $GoodHeap($h_1$0);
			assume $AllocatedObject($h_1$0, $a#3_1$0);
			assert $FieldsNull($h_1$0, $a#3_1$0);
			assert $ReachNull($h_1$0, $a#3_1$0);

			// assert (forall $a:Ref :: $ReachableFromParams#1($h_0$0, $a#0_0$0, $a) ==> $a==$Null);

				assume $a#0_0$0 == $a#0_1$0;
				assume $a#1_0$0 == $a#1_1$0;
				assume $a#2_0$0 == $a#2_1$0;
				assume $a#3_0$0 == $a#3_1$0;

			// procedure body _0 start	
		    x_0$0 := x$0 ;
		    assume $ReadObject($h_0$0, x$0);
		    y_0$0 := y$0 ;
		    assume $ReadObject($h_0$0, y$0);
		    if(true )
		    {
		    	$t#0_0$0 := $a#0_0$0 ;
		    	assume $ReadObject($h_0$0, $a#0_0$0);
		    }
		    if(true )
		    {
		    	xn_0$0 := $t#0_0$0 ;
		    	assume $ReadObject($h_0$0, $t#0_0$0);
		    }
		    if(true )
		    {
		    	$h_0$0:=$Write($h_0$0,x_0$0,$field#v,xn_0$0); assume $GoodHeap($h_0$0);
		    }
		    if(true )
		    {
		    	$t#1_0$0 := $a#1_0$0 ;
		    	assume $ReadObject($h_0$0, $a#1_0$0);
		    }
		    if(true )
		    {
		    	yn_0$0 := $t#1_0$0 ;
		    	assume $ReadObject($h_0$0, $t#1_0$0);
		    }
		    if(true )
		    {
		    	$h_0$0:=$Write($h_0$0,y_0$0,$field#v,yn_0$0); assume $GoodHeap($h_0$0);
		    }
		    if(true )
		    {
		    	$t#2_0$0 := $a#2_0$0 ;
		    	assume $ReadObject($h_0$0, $a#2_0$0);
		    }
		    if(true )
		    {
		    	n_0$0 := $t#2_0$0 ;
		    	assume $ReadObject($h_0$0, $t#2_0$0);
		    }
		    if(true )
		    {
		    	$h_0$0:=$Write($h_0$0,yn_0$0,$field#v,n_0$0); assume $GoodHeap($h_0$0);
		    }
		    if(true )
		    {
		    	$h_0$0:=$Write($h_0$0,xn_0$0,$field#v,n_0$0); assume $GoodHeap($h_0$0);
		    }

		    // procedure body _1 start
		    x_1$0 := x$0 ;
		    assume $ReadObject($h_1$0, x$0);
		    y_1$0 := y$0 ;
		    assume $ReadObject($h_1$0, y$0);
		    if(true )
		    {
		    	$t#0_1$0 := $a#0_1$0 ;
		    	assume $ReadObject($h_1$0, $a#0_1$0);
		    }
		    if(true )
		    {
		    	xn_1$0 := $t#0_1$0 ;
		    	assume $ReadObject($h_1$0, $t#0_1$0);
		    }
		    if(true )
		    {
		    	$h_1$0:=$Write($h_1$0,x_1$0,$field#v,xn_1$0); assume $GoodHeap($h_1$0);
		    }
		    if(true )
		    {
		    	$t#1_1$0 := $a#1_1$0 ;
		    	assume $ReadObject($h_1$0, $a#1_1$0);
		    }
		    if(true )
		    {
		    	yn_1$0 := $t#1_1$0 ;
		    	assume $ReadObject($h_1$0, $t#1_1$0);
		    }
		    if(true )
		    {
		    	$h_1$0:=$Write($h_1$0,y_1$0,$field#v,yn_1$0); assume $GoodHeap($h_1$0);
		    }
		    if(true )
		    {
		    	$t#2_1$0 := $a#2_1$0 ;
		    	assume $ReadObject($h_1$0, $a#2_1$0);
		    }
		    if(true )
		    {
		    	xnn_1$0 := $t#2_1$0 ;
		    	assume $ReadObject($h_1$0, $t#2_1$0);
		    }
		    if(true )
		    {
		    	$t#3_1$0 := $a#3_1$0 ;
		    	assume $ReadObject($h_1$0, $a#3_1$0);
		    }
		    if(true )
		    {
		    	ynn_1$0 := $t#3_1$0 ;
		    	assume $ReadObject($h_1$0, $t#3_1$0);
		    }
		    if(true )
		    {
		    	$h_1$0:=$Write($h_1$0,yn_1$0,$field#v,ynn_1$0); assume $GoodHeap($h_1$0);
		    }
		    if(true )
		    {
		    	$h_1$0:=$Write($h_1$0,xn_1$0,$field#v,xnn_1$0); assume $GoodHeap($h_1$0);
		    }

		    // restore heaps
		    $h_0$1 := $h;
		    $h_1$1 := $h;

		    x$1 := x;
		    y$1 := y;

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
			havoc $a#2_0$1; assume !$Allocated($h_0$1,$a#2_0$1);
			$h_0$1:=$Allocate($h_0$1,$a#2_0$1); assume $GoodHeap($h_0$1);
			assume $AllocatedObject($h_0$1, $a#2_0$1);
			assert $FieldsNull($h_0$1, $a#2_0$1);
			assert $ReachNull($h_0$1, $a#2_0$1);
			havoc $a#3_0$1; assume !$Allocated($h_0$1,$a#3_0$1);
			$h_0$1:=$Allocate($h_0$1,$a#3_0$1); assume $GoodHeap($h_0$1);
			assume $AllocatedObject($h_0$1, $a#3_0$1);
			assert $FieldsNull($h_0$1, $a#3_0$1);
			assert $ReachNull($h_0$1, $a#3_0$1);
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
			havoc $a#2_1$1; assume !$Allocated($h_1$1,$a#2_1$1);
			$h_1$1:=$Allocate($h_1$1,$a#2_1$1); assume $GoodHeap($h_1$1);
			assume $AllocatedObject($h_1$1, $a#2_1$1);
			assert $FieldsNull($h_1$1, $a#2_1$1);
			assert $ReachNull($h_1$1, $a#2_1$1);
			havoc $a#3_1$1; assume !$Allocated($h_1$1,$a#3_1$1);
			$h_1$1:=$Allocate($h_1$1,$a#3_1$1); assume $GoodHeap($h_1$1);
			assume $AllocatedObject($h_1$1, $a#3_1$1);
			assert $FieldsNull($h_1$1, $a#3_1$1);
			assert $ReachNull($h_1$1, $a#3_1$1);

			// assert (forall $a:Ref :: $ReachableFromParams#1($h_0$0, $a#0_0$0, $a) ==> $a==$Null);

				assume $a#1_0$1 == $a#0_1$1;
				assume $a#0_0$1 == $a#1_1$1;
				assume $a#2_0$1 == $a#2_1$1;
				assume $a#3_0$1 == $a#3_1$1;

			// procedure body _0 start	
		    x_0$1 := x$1 ;
		    assume $ReadObject($h_0$1, x$1);
		    y_0$1 := y$1 ;
		    assume $ReadObject($h_0$1, y$1);
		    if(true )
		    {
		    	$t#0_0$1 := $a#0_0$1 ;
		    	assume $ReadObject($h_0$1, $a#0_0$1);
		    }
		    if(true )
		    {
		    	xn_0$1 := $t#0_0$1 ;
		    	assume $ReadObject($h_0$1, $t#0_0$1);
		    }
		    if(true )
		    {
		    	$h_0$1:=$Write($h_0$1,x_0$1,$field#v,xn_0$1); assume $GoodHeap($h_0$1);
		    }
		    if(true )
		    {
		    	$t#1_0$1 := $a#1_0$1 ;
		    	assume $ReadObject($h_0$1, $a#1_0$1);
		    }
		    if(true )
		    {
		    	yn_0$1 := $t#1_0$1 ;
		    	assume $ReadObject($h_0$1, $t#1_0$1);
		    }
		    if(true )
		    {
		    	$h_0$1:=$Write($h_0$1,y_0$1,$field#v,yn_0$1); assume $GoodHeap($h_0$1);
		    }
		    if(true )
		    {
		    	$t#2_0$1 := $a#2_0$1 ;
		    	assume $ReadObject($h_0$1, $a#2_0$1);
		    }
		    if(true )
		    {
		    	n_0$1 := $t#2_0$1 ;
		    	assume $ReadObject($h_0$1, $t#2_0$1);
		    }
		    if(true )
		    {
		    	$h_0$1:=$Write($h_0$1,yn_0$1,$field#v,n_0$1); assume $GoodHeap($h_0$1);
		    }
		    if(true )
		    {
		    	$h_0$1:=$Write($h_0$1,xn_0$1,$field#v,n_0$1); assume $GoodHeap($h_0$1);
		    }

		    // procedure body _1 start
		    x_1$1 := x$1 ;
		    assume $ReadObject($h_1$1, x$1);
		    y_1$1 := y$1 ;
		    assume $ReadObject($h_1$1, y$1);
		    if(true )
		    {
		    	$t#0_1$1 := $a#0_1$1 ;
		    	assume $ReadObject($h_1$1, $a#0_1$1);
		    }
		    if(true )
		    {
		    	xn_1$1 := $t#0_1$1 ;
		    	assume $ReadObject($h_1$1, $t#0_1$1);
		    }
		    if(true )
		    {
		    	$h_1$1:=$Write($h_1$1,x_1$1,$field#v,xn_1$1); assume $GoodHeap($h_1$1);
		    }
		    if(true )
		    {
		    	$t#1_1$1 := $a#1_1$1 ;
		    	assume $ReadObject($h_1$1, $a#1_1$1);
		    }
		    if(true )
		    {
		    	yn_1$1 := $t#1_1$1 ;
		    	assume $ReadObject($h_1$1, $t#1_1$1);
		    }
		    if(true )
		    {
		    	$h_1$1:=$Write($h_1$1,y_1$1,$field#v,yn_1$1); assume $GoodHeap($h_1$1);
		    }
		    if(true )
		    {
		    	$t#2_1$1 := $a#2_1$1 ;
		    	assume $ReadObject($h_1$1, $a#2_1$1);
		    }
		    if(true )
		    {
		    	xnn_1$1 := $t#2_1$1 ;
		    	assume $ReadObject($h_1$1, $t#2_1$1);
		    }
		    if(true )
		    {
		    	$t#3_1$1 := $a#3_1$1 ;
		    	assume $ReadObject($h_1$1, $a#3_1$1);
		    }
		    if(true )
		    {
		    	ynn_1$1 := $t#3_1$1 ;
		    	assume $ReadObject($h_1$1, $t#3_1$1);
		    }
		    if(true )
		    {
		    	$h_1$1:=$Write($h_1$1,yn_1$1,$field#v,ynn_1$1); assume $GoodHeap($h_1$1);
		    }
		    if(true )
		    {
		    	$h_1$1:=$Write($h_1$1,xn_1$1,$field#v,xnn_1$1); assume $GoodHeap($h_1$1);
		    }

		    // restore heaps
		    $h_0$2 := $h;
		    $h_1$2 := $h;

		    x$2 := x;
		    y$2 := y;

		    // prefix start
			havoc $a#0_0$2; assume !$Allocated($h_0$2,$a#0_0$2);
			$h_0$2:=$Allocate($h_0$2,$a#0_0$2); assume $GoodHeap($h_0$2);
			assume $AllocatedObject($h_0$2, $a#0_0$2);
			assert $FieldsNull($h_0$2, $a#0_0$2);
			assert $ReachNull($h_0$2, $a#0_0$2);
			havoc $a#1_0$2; assume !$Allocated($h_0$2,$a#1_0$2);
			$h_0$2:=$Allocate($h_0$2,$a#1_0$2); assume $GoodHeap($h_0$2);
			assume $AllocatedObject($h_0$2, $a#1_0$2);
			assert $FieldsNull($h_0$2, $a#1_0$2);
			assert $ReachNull($h_0$2, $a#1_0$2);
			havoc $a#2_0$2; assume !$Allocated($h_0$2,$a#2_0$2);
			$h_0$2:=$Allocate($h_0$2,$a#2_0$2); assume $GoodHeap($h_0$2);
			assume $AllocatedObject($h_0$2, $a#2_0$2);
			assert $FieldsNull($h_0$2, $a#2_0$2);
			assert $ReachNull($h_0$2, $a#2_0$2);
			havoc $a#3_0$2; assume !$Allocated($h_0$2,$a#3_0$2);
			$h_0$2:=$Allocate($h_0$2,$a#3_0$2); assume $GoodHeap($h_0$2);
			assume $AllocatedObject($h_0$2, $a#3_0$2);
			assert $FieldsNull($h_0$2, $a#3_0$2);
			assert $ReachNull($h_0$2, $a#3_0$2);
			havoc $a#0_1$2; assume !$Allocated($h_1$2,$a#0_1$2);
			$h_1$2:=$Allocate($h_1$2,$a#0_1$2); assume $GoodHeap($h_1$2);
			assume $AllocatedObject($h_1$2, $a#0_1$2);
			assert $FieldsNull($h_1$2, $a#0_1$2);
			assert $ReachNull($h_1$2, $a#0_1$2);
			havoc $a#1_1$2; assume !$Allocated($h_1$2,$a#1_1$2);
			$h_1$2:=$Allocate($h_1$2,$a#1_1$2); assume $GoodHeap($h_1$2);
			assume $AllocatedObject($h_1$2, $a#1_1$2);
			assert $FieldsNull($h_1$2, $a#1_1$2);
			assert $ReachNull($h_1$2, $a#1_1$2);
			havoc $a#2_1$2; assume !$Allocated($h_1$2,$a#2_1$2);
			$h_1$2:=$Allocate($h_1$2,$a#2_1$2); assume $GoodHeap($h_1$2);
			assume $AllocatedObject($h_1$2, $a#2_1$2);
			assert $FieldsNull($h_1$2, $a#2_1$2);
			assert $ReachNull($h_1$2, $a#2_1$2);
			havoc $a#3_1$2; assume !$Allocated($h_1$2,$a#3_1$2);
			$h_1$2:=$Allocate($h_1$2,$a#3_1$2); assume $GoodHeap($h_1$2);
			assume $AllocatedObject($h_1$2, $a#3_1$2);
			assert $FieldsNull($h_1$2, $a#3_1$2);
			assert $ReachNull($h_1$2, $a#3_1$2);

			// assert (forall $a:Ref :: $ReachableFromParams#1($h_0$0, $a#0_0$0, $a) ==> $a==$Null);

				assume $a#2_0$2 == $a#0_1$2;
				assume $a#0_0$2 == $a#1_1$2;
				assume $a#1_0$2 == $a#2_1$2;
				assume $a#3_0$2 == $a#3_1$2;

			// procedure body _0 start	
		    x_0$2 := x$2 ;
		    assume $ReadObject($h_0$2, x$2);
		    y_0$2 := y$2 ;
		    assume $ReadObject($h_0$2, y$2);
		    if(true )
		    {
		    	$t#0_0$2 := $a#0_0$2 ;
		    	assume $ReadObject($h_0$2, $a#0_0$2);
		    }
		    if(true )
		    {
		    	xn_0$2 := $t#0_0$2 ;
		    	assume $ReadObject($h_0$2, $t#0_0$2);
		    }
		    if(true )
		    {
		    	$h_0$2:=$Write($h_0$2,x_0$2,$field#v,xn_0$2); assume $GoodHeap($h_0$2);
		    }
		    if(true )
		    {
		    	$t#1_0$2 := $a#1_0$2 ;
		    	assume $ReadObject($h_0$2, $a#1_0$2);
		    }
		    if(true )
		    {
		    	yn_0$2 := $t#1_0$2 ;
		    	assume $ReadObject($h_0$2, $t#1_0$2);
		    }
		    if(true )
		    {
		    	$h_0$2:=$Write($h_0$2,y_0$2,$field#v,yn_0$2); assume $GoodHeap($h_0$2);
		    }
		    if(true )
		    {
		    	$t#2_0$2 := $a#2_0$2 ;
		    	assume $ReadObject($h_0$2, $a#2_0$2);
		    }
		    if(true )
		    {
		    	n_0$2 := $t#2_0$2 ;
		    	assume $ReadObject($h_0$2, $t#2_0$2);
		    }
		    if(true )
		    {
		    	$h_0$2:=$Write($h_0$2,yn_0$2,$field#v,n_0$2); assume $GoodHeap($h_0$2);
		    }
		    if(true )
		    {
		    	$h_0$2:=$Write($h_0$2,xn_0$2,$field#v,n_0$2); assume $GoodHeap($h_0$2);
		    }

		    // procedure body _1 start
		    x_1$2 := x$2 ;
		    assume $ReadObject($h_1$2, x$2);
		    y_1$2 := y$2 ;
		    assume $ReadObject($h_1$2, y$2);
		    if(true )
		    {
		    	$t#0_1$2 := $a#0_1$2 ;
		    	assume $ReadObject($h_1$2, $a#0_1$2);
		    }
		    if(true )
		    {
		    	xn_1$2 := $t#0_1$2 ;
		    	assume $ReadObject($h_1$2, $t#0_1$2);
		    }
		    if(true )
		    {
		    	$h_1$2:=$Write($h_1$2,x_1$2,$field#v,xn_1$2); assume $GoodHeap($h_1$2);
		    }
		    if(true )
		    {
		    	$t#1_1$2 := $a#1_1$2 ;
		    	assume $ReadObject($h_1$2, $a#1_1$2);
		    }
		    if(true )
		    {
		    	yn_1$2 := $t#1_1$2 ;
		    	assume $ReadObject($h_1$2, $t#1_1$2);
		    }
		    if(true )
		    {
		    	$h_1$2:=$Write($h_1$2,y_1$2,$field#v,yn_1$2); assume $GoodHeap($h_1$2);
		    }
		    if(true )
		    {
		    	$t#2_1$2 := $a#2_1$2 ;
		    	assume $ReadObject($h_1$2, $a#2_1$2);
		    }
		    if(true )
		    {
		    	xnn_1$2 := $t#2_1$2 ;
		    	assume $ReadObject($h_1$2, $t#2_1$2);
		    }
		    if(true )
		    {
		    	$t#3_1$2 := $a#3_1$2 ;
		    	assume $ReadObject($h_1$2, $a#3_1$2);
		    }
		    if(true )
		    {
		    	ynn_1$2 := $t#3_1$2 ;
		    	assume $ReadObject($h_1$2, $t#3_1$2);
		    }
		    if(true )
		    {
		    	$h_1$2:=$Write($h_1$2,yn_1$2,$field#v,ynn_1$2); assume $GoodHeap($h_1$2);
		    }
		    if(true )
		    {
		    	$h_1$2:=$Write($h_1$2,xn_1$2,$field#v,xnn_1$2); assume $GoodHeap($h_1$2);
		    }

		    // restore heaps
		    $h_0$3 := $h;
		    $h_1$3 := $h;

		    x$3 := x;
		    y$3 := y;

		    // prefix start
			havoc $a#0_0$3; assume !$Allocated($h_0$3,$a#0_0$3);
			$h_0$3:=$Allocate($h_0$3,$a#0_0$3); assume $GoodHeap($h_0$3);
			assume $AllocatedObject($h_0$3, $a#0_0$3);
			assert $FieldsNull($h_0$3, $a#0_0$3);
			assert $ReachNull($h_0$3, $a#0_0$3);
			havoc $a#1_0$3; assume !$Allocated($h_0$3,$a#1_0$3);
			$h_0$3:=$Allocate($h_0$3,$a#1_0$3); assume $GoodHeap($h_0$3);
			assume $AllocatedObject($h_0$3, $a#1_0$3);
			assert $FieldsNull($h_0$3, $a#1_0$3);
			assert $ReachNull($h_0$3, $a#1_0$3);
			havoc $a#2_0$3; assume !$Allocated($h_0$3,$a#2_0$3);
			$h_0$3:=$Allocate($h_0$3,$a#2_0$3); assume $GoodHeap($h_0$3);
			assume $AllocatedObject($h_0$3, $a#2_0$3);
			assert $FieldsNull($h_0$3, $a#2_0$3);
			assert $ReachNull($h_0$3, $a#2_0$3);
			havoc $a#3_0$3; assume !$Allocated($h_0$3,$a#3_0$3);
			$h_0$3:=$Allocate($h_0$3,$a#3_0$3); assume $GoodHeap($h_0$3);
			assume $AllocatedObject($h_0$3, $a#3_0$3);
			assert $FieldsNull($h_0$3, $a#3_0$3);
			assert $ReachNull($h_0$3, $a#3_0$3);
			havoc $a#0_1$3; assume !$Allocated($h_1$3,$a#0_1$3);
			$h_1$3:=$Allocate($h_1$3,$a#0_1$3); assume $GoodHeap($h_1$3);
			assume $AllocatedObject($h_1$3, $a#0_1$3);
			assert $FieldsNull($h_1$3, $a#0_1$3);
			assert $ReachNull($h_1$3, $a#0_1$3);
			havoc $a#1_1$3; assume !$Allocated($h_1$3,$a#1_1$3);
			$h_1$3:=$Allocate($h_1$3,$a#1_1$3); assume $GoodHeap($h_1$3);
			assume $AllocatedObject($h_1$3, $a#1_1$3);
			assert $FieldsNull($h_1$3, $a#1_1$3);
			assert $ReachNull($h_1$3, $a#1_1$3);
			havoc $a#2_1$3; assume !$Allocated($h_1$3,$a#2_1$3);
			$h_1$3:=$Allocate($h_1$3,$a#2_1$3); assume $GoodHeap($h_1$3);
			assume $AllocatedObject($h_1$3, $a#2_1$3);
			assert $FieldsNull($h_1$3, $a#2_1$3);
			assert $ReachNull($h_1$3, $a#2_1$3);
			havoc $a#3_1$3; assume !$Allocated($h_1$3,$a#3_1$3);
			$h_1$3:=$Allocate($h_1$3,$a#3_1$3); assume $GoodHeap($h_1$3);
			assume $AllocatedObject($h_1$3, $a#3_1$3);
			assert $FieldsNull($h_1$3, $a#3_1$3);
			assert $ReachNull($h_1$3, $a#3_1$3);

			// assert (forall $a:Ref :: $ReachableFromParams#1($h_0$0, $a#0_0$0, $a) ==> $a==$Null);

				assume $a#0_0$3 == $a#0_1$3;
				assume $a#2_0$3 == $a#1_1$3;
				assume $a#1_0$3 == $a#2_1$3;
				assume $a#3_0$3 == $a#3_1$3;

			// procedure body _0 start	
		    x_0$3 := x$3 ;
		    assume $ReadObject($h_0$3, x$3);
		    y_0$3 := y$3 ;
		    assume $ReadObject($h_0$3, y$3);
		    if(true )
		    {
		    	$t#0_0$3 := $a#0_0$3 ;
		    	assume $ReadObject($h_0$3, $a#0_0$3);
		    }
		    if(true )
		    {
		    	xn_0$3 := $t#0_0$3 ;
		    	assume $ReadObject($h_0$3, $t#0_0$3);
		    }
		    if(true )
		    {
		    	$h_0$3:=$Write($h_0$3,x_0$3,$field#v,xn_0$3); assume $GoodHeap($h_0$3);
		    }
		    if(true )
		    {
		    	$t#1_0$3 := $a#1_0$3 ;
		    	assume $ReadObject($h_0$3, $a#1_0$3);
		    }
		    if(true )
		    {
		    	yn_0$3 := $t#1_0$3 ;
		    	assume $ReadObject($h_0$3, $t#1_0$3);
		    }
		    if(true )
		    {
		    	$h_0$3:=$Write($h_0$3,y_0$3,$field#v,yn_0$3); assume $GoodHeap($h_0$3);
		    }
		    if(true )
		    {
		    	$t#2_0$3 := $a#2_0$3 ;
		    	assume $ReadObject($h_0$3, $a#2_0$3);
		    }
		    if(true )
		    {
		    	n_0$3 := $t#2_0$3 ;
		    	assume $ReadObject($h_0$3, $t#2_0$3);
		    }
		    if(true )
		    {
		    	$h_0$3:=$Write($h_0$3,yn_0$3,$field#v,n_0$3); assume $GoodHeap($h_0$3);
		    }
		    if(true )
		    {
		    	$h_0$3:=$Write($h_0$3,xn_0$3,$field#v,n_0$3); assume $GoodHeap($h_0$3);
		    }

		    // procedure body _1 start
		    x_1$3 := x$3 ;
		    assume $ReadObject($h_1$3, x$3);
		    y_1$3 := y$3 ;
		    assume $ReadObject($h_1$3, y$3);
		    if(true )
		    {
		    	$t#0_1$3 := $a#0_1$3 ;
		    	assume $ReadObject($h_1$3, $a#0_1$3);
		    }
		    if(true )
		    {
		    	xn_1$3 := $t#0_1$3 ;
		    	assume $ReadObject($h_1$3, $t#0_1$3);
		    }
		    if(true )
		    {
		    	$h_1$3:=$Write($h_1$3,x_1$3,$field#v,xn_1$3); assume $GoodHeap($h_1$3);
		    }
		    if(true )
		    {
		    	$t#1_1$3 := $a#1_1$3 ;
		    	assume $ReadObject($h_1$3, $a#1_1$3);
		    }
		    if(true )
		    {
		    	yn_1$3 := $t#1_1$3 ;
		    	assume $ReadObject($h_1$3, $t#1_1$3);
		    }
		    if(true )
		    {
		    	$h_1$3:=$Write($h_1$3,y_1$3,$field#v,yn_1$3); assume $GoodHeap($h_1$3);
		    }
		    if(true )
		    {
		    	$t#2_1$3 := $a#2_1$3 ;
		    	assume $ReadObject($h_1$3, $a#2_1$3);
		    }
		    if(true )
		    {
		    	xnn_1$3 := $t#2_1$3 ;
		    	assume $ReadObject($h_1$3, $t#2_1$3);
		    }
		    if(true )
		    {
		    	$t#3_1$3 := $a#3_1$3 ;
		    	assume $ReadObject($h_1$3, $a#3_1$3);
		    }
		    if(true )
		    {
		    	ynn_1$3 := $t#3_1$3 ;
		    	assume $ReadObject($h_1$3, $t#3_1$3);
		    }
		    if(true )
		    {
		    	$h_1$3:=$Write($h_1$3,yn_1$3,$field#v,ynn_1$3); assume $GoodHeap($h_1$3);
		    }
		    if(true )
		    {
		    	$h_1$3:=$Write($h_1$3,xn_1$3,$field#v,xnn_1$3); assume $GoodHeap($h_1$3);
		    }

		    // restore heaps
		    $h_0$4 := $h;
		    $h_1$4 := $h;

		    x$4 := x;
		    y$4 := y;

		    // prefix start
			havoc $a#0_0$4; assume !$Allocated($h_0$4,$a#0_0$4);
			$h_0$4:=$Allocate($h_0$4,$a#0_0$4); assume $GoodHeap($h_0$4);
			assume $AllocatedObject($h_0$4, $a#0_0$4);
			assert $FieldsNull($h_0$4, $a#0_0$4);
			assert $ReachNull($h_0$4, $a#0_0$4);
			havoc $a#1_0$4; assume !$Allocated($h_0$4,$a#1_0$4);
			$h_0$4:=$Allocate($h_0$4,$a#1_0$4); assume $GoodHeap($h_0$4);
			assume $AllocatedObject($h_0$4, $a#1_0$4);
			assert $FieldsNull($h_0$4, $a#1_0$4);
			assert $ReachNull($h_0$4, $a#1_0$4);
			havoc $a#2_0$4; assume !$Allocated($h_0$4,$a#2_0$4);
			$h_0$4:=$Allocate($h_0$4,$a#2_0$4); assume $GoodHeap($h_0$4);
			assume $AllocatedObject($h_0$4, $a#2_0$4);
			assert $FieldsNull($h_0$4, $a#2_0$4);
			assert $ReachNull($h_0$4, $a#2_0$4);
			havoc $a#3_0$4; assume !$Allocated($h_0$4,$a#3_0$4);
			$h_0$4:=$Allocate($h_0$4,$a#3_0$4); assume $GoodHeap($h_0$4);
			assume $AllocatedObject($h_0$4, $a#3_0$4);
			assert $FieldsNull($h_0$4, $a#3_0$4);
			assert $ReachNull($h_0$4, $a#3_0$4);
			havoc $a#0_1$4; assume !$Allocated($h_1$4,$a#0_1$4);
			$h_1$4:=$Allocate($h_1$4,$a#0_1$4); assume $GoodHeap($h_1$4);
			assume $AllocatedObject($h_1$4, $a#0_1$4);
			assert $FieldsNull($h_1$4, $a#0_1$4);
			assert $ReachNull($h_1$4, $a#0_1$4);
			havoc $a#1_1$4; assume !$Allocated($h_1$4,$a#1_1$4);
			$h_1$4:=$Allocate($h_1$4,$a#1_1$4); assume $GoodHeap($h_1$4);
			assume $AllocatedObject($h_1$4, $a#1_1$4);
			assert $FieldsNull($h_1$4, $a#1_1$4);
			assert $ReachNull($h_1$4, $a#1_1$4);
			havoc $a#2_1$4; assume !$Allocated($h_1$4,$a#2_1$4);
			$h_1$4:=$Allocate($h_1$4,$a#2_1$4); assume $GoodHeap($h_1$4);
			assume $AllocatedObject($h_1$4, $a#2_1$4);
			assert $FieldsNull($h_1$4, $a#2_1$4);
			assert $ReachNull($h_1$4, $a#2_1$4);
			havoc $a#3_1$4; assume !$Allocated($h_1$4,$a#3_1$4);
			$h_1$4:=$Allocate($h_1$4,$a#3_1$4); assume $GoodHeap($h_1$4);
			assume $AllocatedObject($h_1$4, $a#3_1$4);
			assert $FieldsNull($h_1$4, $a#3_1$4);
			assert $ReachNull($h_1$4, $a#3_1$4);

			// assert (forall $a:Ref :: $ReachableFromParams#1($h_0$0, $a#0_0$0, $a) ==> $a==$Null);

				assume $a#1_0$4 == $a#0_1$4;
				assume $a#2_0$4 == $a#1_1$4;
				assume $a#0_0$4 == $a#2_1$4;
				assume $a#3_0$4 == $a#3_1$4;

			// procedure body _0 start	
		    x_0$4 := x$4 ;
		    assume $ReadObject($h_0$4, x$4);
		    y_0$4 := y$4 ;
		    assume $ReadObject($h_0$4, y$4);
		    if(true )
		    {
		    	$t#0_0$4 := $a#0_0$4 ;
		    	assume $ReadObject($h_0$4, $a#0_0$4);
		    }
		    if(true )
		    {
		    	xn_0$4 := $t#0_0$4 ;
		    	assume $ReadObject($h_0$4, $t#0_0$4);
		    }
		    if(true )
		    {
		    	$h_0$4:=$Write($h_0$4,x_0$4,$field#v,xn_0$4); assume $GoodHeap($h_0$4);
		    }
		    if(true )
		    {
		    	$t#1_0$4 := $a#1_0$4 ;
		    	assume $ReadObject($h_0$4, $a#1_0$4);
		    }
		    if(true )
		    {
		    	yn_0$4 := $t#1_0$4 ;
		    	assume $ReadObject($h_0$4, $t#1_0$4);
		    }
		    if(true )
		    {
		    	$h_0$4:=$Write($h_0$4,y_0$4,$field#v,yn_0$4); assume $GoodHeap($h_0$4);
		    }
		    if(true )
		    {
		    	$t#2_0$4 := $a#2_0$4 ;
		    	assume $ReadObject($h_0$4, $a#2_0$4);
		    }
		    if(true )
		    {
		    	n_0$4 := $t#2_0$4 ;
		    	assume $ReadObject($h_0$4, $t#2_0$4);
		    }
		    if(true )
		    {
		    	$h_0$4:=$Write($h_0$4,yn_0$4,$field#v,n_0$4); assume $GoodHeap($h_0$4);
		    }
		    if(true )
		    {
		    	$h_0$4:=$Write($h_0$4,xn_0$4,$field#v,n_0$4); assume $GoodHeap($h_0$4);
		    }

		    // procedure body _1 start
		    x_1$4 := x$4 ;
		    assume $ReadObject($h_1$4, x$4);
		    y_1$4 := y$4 ;
		    assume $ReadObject($h_1$4, y$4);
		    if(true )
		    {
		    	$t#0_1$4 := $a#0_1$4 ;
		    	assume $ReadObject($h_1$4, $a#0_1$4);
		    }
		    if(true )
		    {
		    	xn_1$4 := $t#0_1$4 ;
		    	assume $ReadObject($h_1$4, $t#0_1$4);
		    }
		    if(true )
		    {
		    	$h_1$4:=$Write($h_1$4,x_1$4,$field#v,xn_1$4); assume $GoodHeap($h_1$4);
		    }
		    if(true )
		    {
		    	$t#1_1$4 := $a#1_1$4 ;
		    	assume $ReadObject($h_1$4, $a#1_1$4);
		    }
		    if(true )
		    {
		    	yn_1$4 := $t#1_1$4 ;
		    	assume $ReadObject($h_1$4, $t#1_1$4);
		    }
		    if(true )
		    {
		    	$h_1$4:=$Write($h_1$4,y_1$4,$field#v,yn_1$4); assume $GoodHeap($h_1$4);
		    }
		    if(true )
		    {
		    	$t#2_1$4 := $a#2_1$4 ;
		    	assume $ReadObject($h_1$4, $a#2_1$4);
		    }
		    if(true )
		    {
		    	xnn_1$4 := $t#2_1$4 ;
		    	assume $ReadObject($h_1$4, $t#2_1$4);
		    }
		    if(true )
		    {
		    	$t#3_1$4 := $a#3_1$4 ;
		    	assume $ReadObject($h_1$4, $a#3_1$4);
		    }
		    if(true )
		    {
		    	ynn_1$4 := $t#3_1$4 ;
		    	assume $ReadObject($h_1$4, $t#3_1$4);
		    }
		    if(true )
		    {
		    	$h_1$4:=$Write($h_1$4,yn_1$4,$field#v,ynn_1$4); assume $GoodHeap($h_1$4);
		    }
		    if(true )
		    {
		    	$h_1$4:=$Write($h_1$4,xn_1$4,$field#v,xnn_1$4); assume $GoodHeap($h_1$4);
		    }

		    // restore heaps
		    $h_0$5 := $h;
		    $h_1$5 := $h;

		    x$5 := x;
		    y$5 := y;

		    // prefix start
			havoc $a#0_0$5; assume !$Allocated($h_0$5,$a#0_0$5);
			$h_0$5:=$Allocate($h_0$5,$a#0_0$5); assume $GoodHeap($h_0$5);
			assume $AllocatedObject($h_0$5, $a#0_0$5);
			assert $FieldsNull($h_0$5, $a#0_0$5);
			assert $ReachNull($h_0$5, $a#0_0$5);
			havoc $a#1_0$5; assume !$Allocated($h_0$5,$a#1_0$5);
			$h_0$5:=$Allocate($h_0$5,$a#1_0$5); assume $GoodHeap($h_0$5);
			assume $AllocatedObject($h_0$5, $a#1_0$5);
			assert $FieldsNull($h_0$5, $a#1_0$5);
			assert $ReachNull($h_0$5, $a#1_0$5);
			havoc $a#2_0$5; assume !$Allocated($h_0$5,$a#2_0$5);
			$h_0$5:=$Allocate($h_0$5,$a#2_0$5); assume $GoodHeap($h_0$5);
			assume $AllocatedObject($h_0$5, $a#2_0$5);
			assert $FieldsNull($h_0$5, $a#2_0$5);
			assert $ReachNull($h_0$5, $a#2_0$5);
			havoc $a#3_0$5; assume !$Allocated($h_0$5,$a#3_0$5);
			$h_0$5:=$Allocate($h_0$5,$a#3_0$5); assume $GoodHeap($h_0$5);
			assume $AllocatedObject($h_0$5, $a#3_0$5);
			assert $FieldsNull($h_0$5, $a#3_0$5);
			assert $ReachNull($h_0$5, $a#3_0$5);
			havoc $a#0_1$5; assume !$Allocated($h_1$5,$a#0_1$5);
			$h_1$5:=$Allocate($h_1$5,$a#0_1$5); assume $GoodHeap($h_1$5);
			assume $AllocatedObject($h_1$5, $a#0_1$5);
			assert $FieldsNull($h_1$5, $a#0_1$5);
			assert $ReachNull($h_1$5, $a#0_1$5);
			havoc $a#1_1$5; assume !$Allocated($h_1$5,$a#1_1$5);
			$h_1$5:=$Allocate($h_1$5,$a#1_1$5); assume $GoodHeap($h_1$5);
			assume $AllocatedObject($h_1$5, $a#1_1$5);
			assert $FieldsNull($h_1$5, $a#1_1$5);
			assert $ReachNull($h_1$5, $a#1_1$5);
			havoc $a#2_1$5; assume !$Allocated($h_1$5,$a#2_1$5);
			$h_1$5:=$Allocate($h_1$5,$a#2_1$5); assume $GoodHeap($h_1$5);
			assume $AllocatedObject($h_1$5, $a#2_1$5);
			assert $FieldsNull($h_1$5, $a#2_1$5);
			assert $ReachNull($h_1$5, $a#2_1$5);
			havoc $a#3_1$5; assume !$Allocated($h_1$5,$a#3_1$5);
			$h_1$5:=$Allocate($h_1$5,$a#3_1$5); assume $GoodHeap($h_1$5);
			assume $AllocatedObject($h_1$5, $a#3_1$5);
			assert $FieldsNull($h_1$5, $a#3_1$5);
			assert $ReachNull($h_1$5, $a#3_1$5);

			// assert (forall $a:Ref :: $ReachableFromParams#1($h_0$0, $a#0_0$0, $a) ==> $a==$Null);

				assume $a#2_0$5 == $a#0_1$5;
				assume $a#1_0$5 == $a#1_1$5;
				assume $a#0_0$5 == $a#2_1$5;
				assume $a#3_0$5 == $a#3_1$5;

			// procedure body _0 start	
		    x_0$5 := x$5 ;
		    assume $ReadObject($h_0$5, x$5);
		    y_0$5 := y$5 ;
		    assume $ReadObject($h_0$5, y$5);
		    if(true )
		    {
		    	$t#0_0$5 := $a#0_0$5 ;
		    	assume $ReadObject($h_0$5, $a#0_0$5);
		    }
		    if(true )
		    {
		    	xn_0$5 := $t#0_0$5 ;
		    	assume $ReadObject($h_0$5, $t#0_0$5);
		    }
		    if(true )
		    {
		    	$h_0$5:=$Write($h_0$5,x_0$5,$field#v,xn_0$5); assume $GoodHeap($h_0$5);
		    }
		    if(true )
		    {
		    	$t#1_0$5 := $a#1_0$5 ;
		    	assume $ReadObject($h_0$5, $a#1_0$5);
		    }
		    if(true )
		    {
		    	yn_0$5 := $t#1_0$5 ;
		    	assume $ReadObject($h_0$5, $t#1_0$5);
		    }
		    if(true )
		    {
		    	$h_0$5:=$Write($h_0$5,y_0$5,$field#v,yn_0$5); assume $GoodHeap($h_0$5);
		    }
		    if(true )
		    {
		    	$t#2_0$5 := $a#2_0$5 ;
		    	assume $ReadObject($h_0$5, $a#2_0$5);
		    }
		    if(true )
		    {
		    	n_0$5 := $t#2_0$5 ;
		    	assume $ReadObject($h_0$5, $t#2_0$5);
		    }
		    if(true )
		    {
		    	$h_0$5:=$Write($h_0$5,yn_0$5,$field#v,n_0$5); assume $GoodHeap($h_0$5);
		    }
		    if(true )
		    {
		    	$h_0$5:=$Write($h_0$5,xn_0$5,$field#v,n_0$5); assume $GoodHeap($h_0$5);
		    }

		    // procedure body _1 start
		    x_1$5 := x$5 ;
		    assume $ReadObject($h_1$5, x$5);
		    y_1$5 := y$5 ;
		    assume $ReadObject($h_1$5, y$5);
		    if(true )
		    {
		    	$t#0_1$5 := $a#0_1$5 ;
		    	assume $ReadObject($h_1$5, $a#0_1$5);
		    }
		    if(true )
		    {
		    	xn_1$5 := $t#0_1$5 ;
		    	assume $ReadObject($h_1$5, $t#0_1$5);
		    }
		    if(true )
		    {
		    	$h_1$5:=$Write($h_1$5,x_1$5,$field#v,xn_1$5); assume $GoodHeap($h_1$5);
		    }
		    if(true )
		    {
		    	$t#1_1$5 := $a#1_1$5 ;
		    	assume $ReadObject($h_1$5, $a#1_1$5);
		    }
		    if(true )
		    {
		    	yn_1$5 := $t#1_1$5 ;
		    	assume $ReadObject($h_1$5, $t#1_1$5);
		    }
		    if(true )
		    {
		    	$h_1$5:=$Write($h_1$5,y_1$5,$field#v,yn_1$5); assume $GoodHeap($h_1$5);
		    }
		    if(true )
		    {
		    	$t#2_1$5 := $a#2_1$5 ;
		    	assume $ReadObject($h_1$5, $a#2_1$5);
		    }
		    if(true )
		    {
		    	xnn_1$5 := $t#2_1$5 ;
		    	assume $ReadObject($h_1$5, $t#2_1$5);
		    }
		    if(true )
		    {
		    	$t#3_1$5 := $a#3_1$5 ;
		    	assume $ReadObject($h_1$5, $a#3_1$5);
		    }
		    if(true )
		    {
		    	ynn_1$5 := $t#3_1$5 ;
		    	assume $ReadObject($h_1$5, $t#3_1$5);
		    }
		    if(true )
		    {
		    	$h_1$5:=$Write($h_1$5,yn_1$5,$field#v,ynn_1$5); assume $GoodHeap($h_1$5);
		    }
		    if(true )
		    {
		    	$h_1$5:=$Write($h_1$5,xn_1$5,$field#v,xnn_1$5); assume $GoodHeap($h_1$5);
		    }

		    // restore heaps
		    $h_0$6 := $h;
		    $h_1$6 := $h;

		    x$6 := x;
		    y$6 := y;

		    // prefix start
			havoc $a#0_0$6; assume !$Allocated($h_0$6,$a#0_0$6);
			$h_0$6:=$Allocate($h_0$6,$a#0_0$6); assume $GoodHeap($h_0$6);
			assume $AllocatedObject($h_0$6, $a#0_0$6);
			assert $FieldsNull($h_0$6, $a#0_0$6);
			assert $ReachNull($h_0$6, $a#0_0$6);
			havoc $a#1_0$6; assume !$Allocated($h_0$6,$a#1_0$6);
			$h_0$6:=$Allocate($h_0$6,$a#1_0$6); assume $GoodHeap($h_0$6);
			assume $AllocatedObject($h_0$6, $a#1_0$6);
			assert $FieldsNull($h_0$6, $a#1_0$6);
			assert $ReachNull($h_0$6, $a#1_0$6);
			havoc $a#2_0$6; assume !$Allocated($h_0$6,$a#2_0$6);
			$h_0$6:=$Allocate($h_0$6,$a#2_0$6); assume $GoodHeap($h_0$6);
			assume $AllocatedObject($h_0$6, $a#2_0$6);
			assert $FieldsNull($h_0$6, $a#2_0$6);
			assert $ReachNull($h_0$6, $a#2_0$6);
			havoc $a#3_0$6; assume !$Allocated($h_0$6,$a#3_0$6);
			$h_0$6:=$Allocate($h_0$6,$a#3_0$6); assume $GoodHeap($h_0$6);
			assume $AllocatedObject($h_0$6, $a#3_0$6);
			assert $FieldsNull($h_0$6, $a#3_0$6);
			assert $ReachNull($h_0$6, $a#3_0$6);
			havoc $a#0_1$6; assume !$Allocated($h_1$6,$a#0_1$6);
			$h_1$6:=$Allocate($h_1$6,$a#0_1$6); assume $GoodHeap($h_1$6);
			assume $AllocatedObject($h_1$6, $a#0_1$6);
			assert $FieldsNull($h_1$6, $a#0_1$6);
			assert $ReachNull($h_1$6, $a#0_1$6);
			havoc $a#1_1$6; assume !$Allocated($h_1$6,$a#1_1$6);
			$h_1$6:=$Allocate($h_1$6,$a#1_1$6); assume $GoodHeap($h_1$6);
			assume $AllocatedObject($h_1$6, $a#1_1$6);
			assert $FieldsNull($h_1$6, $a#1_1$6);
			assert $ReachNull($h_1$6, $a#1_1$6);
			havoc $a#2_1$6; assume !$Allocated($h_1$6,$a#2_1$6);
			$h_1$6:=$Allocate($h_1$6,$a#2_1$6); assume $GoodHeap($h_1$6);
			assume $AllocatedObject($h_1$6, $a#2_1$6);
			assert $FieldsNull($h_1$6, $a#2_1$6);
			assert $ReachNull($h_1$6, $a#2_1$6);
			havoc $a#3_1$6; assume !$Allocated($h_1$6,$a#3_1$6);
			$h_1$6:=$Allocate($h_1$6,$a#3_1$6); assume $GoodHeap($h_1$6);
			assume $AllocatedObject($h_1$6, $a#3_1$6);
			assert $FieldsNull($h_1$6, $a#3_1$6);
			assert $ReachNull($h_1$6, $a#3_1$6);

			// assert (forall $a:Ref :: $ReachableFromParams#1($h_0$0, $a#0_0$0, $a) ==> $a==$Null);

				assume $a#3_0$6 == $a#0_1$6;
				assume $a#1_0$6 == $a#1_1$6;
				assume $a#0_0$6 == $a#2_1$6;
				assume $a#2_0$6 == $a#3_1$6;

			// procedure body _0 start	
		    x_0$6 := x$6 ;
		    assume $ReadObject($h_0$6, x$6);
		    y_0$6 := y$6 ;
		    assume $ReadObject($h_0$6, y$6);
		    if(true )
		    {
		    	$t#0_0$6 := $a#0_0$6 ;
		    	assume $ReadObject($h_0$6, $a#0_0$6);
		    }
		    if(true )
		    {
		    	xn_0$6 := $t#0_0$6 ;
		    	assume $ReadObject($h_0$6, $t#0_0$6);
		    }
		    if(true )
		    {
		    	$h_0$6:=$Write($h_0$6,x_0$6,$field#v,xn_0$6); assume $GoodHeap($h_0$6);
		    }
		    if(true )
		    {
		    	$t#1_0$6 := $a#1_0$6 ;
		    	assume $ReadObject($h_0$6, $a#1_0$6);
		    }
		    if(true )
		    {
		    	yn_0$6 := $t#1_0$6 ;
		    	assume $ReadObject($h_0$6, $t#1_0$6);
		    }
		    if(true )
		    {
		    	$h_0$6:=$Write($h_0$6,y_0$6,$field#v,yn_0$6); assume $GoodHeap($h_0$6);
		    }
		    if(true )
		    {
		    	$t#2_0$6 := $a#2_0$6 ;
		    	assume $ReadObject($h_0$6, $a#2_0$6);
		    }
		    if(true )
		    {
		    	n_0$6 := $t#2_0$6 ;
		    	assume $ReadObject($h_0$6, $t#2_0$6);
		    }
		    if(true )
		    {
		    	$h_0$6:=$Write($h_0$6,yn_0$6,$field#v,n_0$6); assume $GoodHeap($h_0$6);
		    }
		    if(true )
		    {
		    	$h_0$6:=$Write($h_0$6,xn_0$6,$field#v,n_0$6); assume $GoodHeap($h_0$6);
		    }

		    // procedure body _1 start
		    x_1$6 := x$6 ;
		    assume $ReadObject($h_1$6, x$6);
		    y_1$6 := y$6 ;
		    assume $ReadObject($h_1$6, y$6);
		    if(true )
		    {
		    	$t#0_1$6 := $a#0_1$6 ;
		    	assume $ReadObject($h_1$6, $a#0_1$6);
		    }
		    if(true )
		    {
		    	xn_1$6 := $t#0_1$6 ;
		    	assume $ReadObject($h_1$6, $t#0_1$6);
		    }
		    if(true )
		    {
		    	$h_1$6:=$Write($h_1$6,x_1$6,$field#v,xn_1$6); assume $GoodHeap($h_1$6);
		    }
		    if(true )
		    {
		    	$t#1_1$6 := $a#1_1$6 ;
		    	assume $ReadObject($h_1$6, $a#1_1$6);
		    }
		    if(true )
		    {
		    	yn_1$6 := $t#1_1$6 ;
		    	assume $ReadObject($h_1$6, $t#1_1$6);
		    }
		    if(true )
		    {
		    	$h_1$6:=$Write($h_1$6,y_1$6,$field#v,yn_1$6); assume $GoodHeap($h_1$6);
		    }
		    if(true )
		    {
		    	$t#2_1$6 := $a#2_1$6 ;
		    	assume $ReadObject($h_1$6, $a#2_1$6);
		    }
		    if(true )
		    {
		    	xnn_1$6 := $t#2_1$6 ;
		    	assume $ReadObject($h_1$6, $t#2_1$6);
		    }
		    if(true )
		    {
		    	$t#3_1$6 := $a#3_1$6 ;
		    	assume $ReadObject($h_1$6, $a#3_1$6);
		    }
		    if(true )
		    {
		    	ynn_1$6 := $t#3_1$6 ;
		    	assume $ReadObject($h_1$6, $t#3_1$6);
		    }
		    if(true )
		    {
		    	$h_1$6:=$Write($h_1$6,yn_1$6,$field#v,ynn_1$6); assume $GoodHeap($h_1$6);
		    }
		    if(true )
		    {
		    	$h_1$6:=$Write($h_1$6,xn_1$6,$field#v,xnn_1$6); assume $GoodHeap($h_1$6);
		    }

		    // restore heaps
		    $h_0$7 := $h;
		    $h_1$7 := $h;

		    x$7 := x;
		    y$7 := y;

		    // prefix start
			havoc $a#0_0$7; assume !$Allocated($h_0$7,$a#0_0$7);
			$h_0$7:=$Allocate($h_0$7,$a#0_0$7); assume $GoodHeap($h_0$7);
			assume $AllocatedObject($h_0$7, $a#0_0$7);
			assert $FieldsNull($h_0$7, $a#0_0$7);
			assert $ReachNull($h_0$7, $a#0_0$7);
			havoc $a#1_0$7; assume !$Allocated($h_0$7,$a#1_0$7);
			$h_0$7:=$Allocate($h_0$7,$a#1_0$7); assume $GoodHeap($h_0$7);
			assume $AllocatedObject($h_0$7, $a#1_0$7);
			assert $FieldsNull($h_0$7, $a#1_0$7);
			assert $ReachNull($h_0$7, $a#1_0$7);
			havoc $a#2_0$7; assume !$Allocated($h_0$7,$a#2_0$7);
			$h_0$7:=$Allocate($h_0$7,$a#2_0$7); assume $GoodHeap($h_0$7);
			assume $AllocatedObject($h_0$7, $a#2_0$7);
			assert $FieldsNull($h_0$7, $a#2_0$7);
			assert $ReachNull($h_0$7, $a#2_0$7);
			havoc $a#3_0$7; assume !$Allocated($h_0$7,$a#3_0$7);
			$h_0$7:=$Allocate($h_0$7,$a#3_0$7); assume $GoodHeap($h_0$7);
			assume $AllocatedObject($h_0$7, $a#3_0$7);
			assert $FieldsNull($h_0$7, $a#3_0$7);
			assert $ReachNull($h_0$7, $a#3_0$7);
			havoc $a#0_1$7; assume !$Allocated($h_1$7,$a#0_1$7);
			$h_1$7:=$Allocate($h_1$7,$a#0_1$7); assume $GoodHeap($h_1$7);
			assume $AllocatedObject($h_1$7, $a#0_1$7);
			assert $FieldsNull($h_1$7, $a#0_1$7);
			assert $ReachNull($h_1$7, $a#0_1$7);
			havoc $a#1_1$7; assume !$Allocated($h_1$7,$a#1_1$7);
			$h_1$7:=$Allocate($h_1$7,$a#1_1$7); assume $GoodHeap($h_1$7);
			assume $AllocatedObject($h_1$7, $a#1_1$7);
			assert $FieldsNull($h_1$7, $a#1_1$7);
			assert $ReachNull($h_1$7, $a#1_1$7);
			havoc $a#2_1$7; assume !$Allocated($h_1$7,$a#2_1$7);
			$h_1$7:=$Allocate($h_1$7,$a#2_1$7); assume $GoodHeap($h_1$7);
			assume $AllocatedObject($h_1$7, $a#2_1$7);
			assert $FieldsNull($h_1$7, $a#2_1$7);
			assert $ReachNull($h_1$7, $a#2_1$7);
			havoc $a#3_1$7; assume !$Allocated($h_1$7,$a#3_1$7);
			$h_1$7:=$Allocate($h_1$7,$a#3_1$7); assume $GoodHeap($h_1$7);
			assume $AllocatedObject($h_1$7, $a#3_1$7);
			assert $FieldsNull($h_1$7, $a#3_1$7);
			assert $ReachNull($h_1$7, $a#3_1$7);

			// assert (forall $a:Ref :: $ReachableFromParams#1($h_0$0, $a#0_0$0, $a) ==> $a==$Null);

				assume $a#1_0$7 == $a#0_1$7;
				assume $a#3_0$7 == $a#1_1$7;
				assume $a#0_0$7 == $a#2_1$7;
				assume $a#2_0$7 == $a#3_1$7;

			// procedure body _0 start	
		    x_0$7 := x$7 ;
		    assume $ReadObject($h_0$7, x$7);
		    y_0$7 := y$7 ;
		    assume $ReadObject($h_0$7, y$7);
		    if(true )
		    {
		    	$t#0_0$7 := $a#0_0$7 ;
		    	assume $ReadObject($h_0$7, $a#0_0$7);
		    }
		    if(true )
		    {
		    	xn_0$7 := $t#0_0$7 ;
		    	assume $ReadObject($h_0$7, $t#0_0$7);
		    }
		    if(true )
		    {
		    	$h_0$7:=$Write($h_0$7,x_0$7,$field#v,xn_0$7); assume $GoodHeap($h_0$7);
		    }
		    if(true )
		    {
		    	$t#1_0$7 := $a#1_0$7 ;
		    	assume $ReadObject($h_0$7, $a#1_0$7);
		    }
		    if(true )
		    {
		    	yn_0$7 := $t#1_0$7 ;
		    	assume $ReadObject($h_0$7, $t#1_0$7);
		    }
		    if(true )
		    {
		    	$h_0$7:=$Write($h_0$7,y_0$7,$field#v,yn_0$7); assume $GoodHeap($h_0$7);
		    }
		    if(true )
		    {
		    	$t#2_0$7 := $a#2_0$7 ;
		    	assume $ReadObject($h_0$7, $a#2_0$7);
		    }
		    if(true )
		    {
		    	n_0$7 := $t#2_0$7 ;
		    	assume $ReadObject($h_0$7, $t#2_0$7);
		    }
		    if(true )
		    {
		    	$h_0$7:=$Write($h_0$7,yn_0$7,$field#v,n_0$7); assume $GoodHeap($h_0$7);
		    }
		    if(true )
		    {
		    	$h_0$7:=$Write($h_0$7,xn_0$7,$field#v,n_0$7); assume $GoodHeap($h_0$7);
		    }

		    // procedure body _1 start
		    x_1$7 := x$7 ;
		    assume $ReadObject($h_1$7, x$7);
		    y_1$7 := y$7 ;
		    assume $ReadObject($h_1$7, y$7);
		    if(true )
		    {
		    	$t#0_1$7 := $a#0_1$7 ;
		    	assume $ReadObject($h_1$7, $a#0_1$7);
		    }
		    if(true )
		    {
		    	xn_1$7 := $t#0_1$7 ;
		    	assume $ReadObject($h_1$7, $t#0_1$7);
		    }
		    if(true )
		    {
		    	$h_1$7:=$Write($h_1$7,x_1$7,$field#v,xn_1$7); assume $GoodHeap($h_1$7);
		    }
		    if(true )
		    {
		    	$t#1_1$7 := $a#1_1$7 ;
		    	assume $ReadObject($h_1$7, $a#1_1$7);
		    }
		    if(true )
		    {
		    	yn_1$7 := $t#1_1$7 ;
		    	assume $ReadObject($h_1$7, $t#1_1$7);
		    }
		    if(true )
		    {
		    	$h_1$7:=$Write($h_1$7,y_1$7,$field#v,yn_1$7); assume $GoodHeap($h_1$7);
		    }
		    if(true )
		    {
		    	$t#2_1$7 := $a#2_1$7 ;
		    	assume $ReadObject($h_1$7, $a#2_1$7);
		    }
		    if(true )
		    {
		    	xnn_1$7 := $t#2_1$7 ;
		    	assume $ReadObject($h_1$7, $t#2_1$7);
		    }
		    if(true )
		    {
		    	$t#3_1$7 := $a#3_1$7 ;
		    	assume $ReadObject($h_1$7, $a#3_1$7);
		    }
		    if(true )
		    {
		    	ynn_1$7 := $t#3_1$7 ;
		    	assume $ReadObject($h_1$7, $t#3_1$7);
		    }
		    if(true )
		    {
		    	$h_1$7:=$Write($h_1$7,yn_1$7,$field#v,ynn_1$7); assume $GoodHeap($h_1$7);
		    }
		    if(true )
		    {
		    	$h_1$7:=$Write($h_1$7,xn_1$7,$field#v,xnn_1$7); assume $GoodHeap($h_1$7);
		    }

		    // restore heaps
		    $h_0$8 := $h;
		    $h_1$8 := $h;

		    x$8 := x;
		    y$8 := y;

		    // prefix start
			havoc $a#0_0$8; assume !$Allocated($h_0$8,$a#0_0$8);
			$h_0$8:=$Allocate($h_0$8,$a#0_0$8); assume $GoodHeap($h_0$8);
			assume $AllocatedObject($h_0$8, $a#0_0$8);
			assert $FieldsNull($h_0$8, $a#0_0$8);
			assert $ReachNull($h_0$8, $a#0_0$8);
			havoc $a#1_0$8; assume !$Allocated($h_0$8,$a#1_0$8);
			$h_0$8:=$Allocate($h_0$8,$a#1_0$8); assume $GoodHeap($h_0$8);
			assume $AllocatedObject($h_0$8, $a#1_0$8);
			assert $FieldsNull($h_0$8, $a#1_0$8);
			assert $ReachNull($h_0$8, $a#1_0$8);
			havoc $a#2_0$8; assume !$Allocated($h_0$8,$a#2_0$8);
			$h_0$8:=$Allocate($h_0$8,$a#2_0$8); assume $GoodHeap($h_0$8);
			assume $AllocatedObject($h_0$8, $a#2_0$8);
			assert $FieldsNull($h_0$8, $a#2_0$8);
			assert $ReachNull($h_0$8, $a#2_0$8);
			havoc $a#3_0$8; assume !$Allocated($h_0$8,$a#3_0$8);
			$h_0$8:=$Allocate($h_0$8,$a#3_0$8); assume $GoodHeap($h_0$8);
			assume $AllocatedObject($h_0$8, $a#3_0$8);
			assert $FieldsNull($h_0$8, $a#3_0$8);
			assert $ReachNull($h_0$8, $a#3_0$8);
			havoc $a#0_1$8; assume !$Allocated($h_1$8,$a#0_1$8);
			$h_1$8:=$Allocate($h_1$8,$a#0_1$8); assume $GoodHeap($h_1$8);
			assume $AllocatedObject($h_1$8, $a#0_1$8);
			assert $FieldsNull($h_1$8, $a#0_1$8);
			assert $ReachNull($h_1$8, $a#0_1$8);
			havoc $a#1_1$8; assume !$Allocated($h_1$8,$a#1_1$8);
			$h_1$8:=$Allocate($h_1$8,$a#1_1$8); assume $GoodHeap($h_1$8);
			assume $AllocatedObject($h_1$8, $a#1_1$8);
			assert $FieldsNull($h_1$8, $a#1_1$8);
			assert $ReachNull($h_1$8, $a#1_1$8);
			havoc $a#2_1$8; assume !$Allocated($h_1$8,$a#2_1$8);
			$h_1$8:=$Allocate($h_1$8,$a#2_1$8); assume $GoodHeap($h_1$8);
			assume $AllocatedObject($h_1$8, $a#2_1$8);
			assert $FieldsNull($h_1$8, $a#2_1$8);
			assert $ReachNull($h_1$8, $a#2_1$8);
			havoc $a#3_1$8; assume !$Allocated($h_1$8,$a#3_1$8);
			$h_1$8:=$Allocate($h_1$8,$a#3_1$8); assume $GoodHeap($h_1$8);
			assume $AllocatedObject($h_1$8, $a#3_1$8);
			assert $FieldsNull($h_1$8, $a#3_1$8);
			assert $ReachNull($h_1$8, $a#3_1$8);

			// assert (forall $a:Ref :: $ReachableFromParams#1($h_0$0, $a#0_0$0, $a) ==> $a==$Null);

				assume $a#0_0$8 == $a#0_1$8;
				assume $a#3_0$8 == $a#1_1$8;
				assume $a#1_0$8 == $a#2_1$8;
				assume $a#2_0$8 == $a#3_1$8;

			// procedure body _0 start	
		    x_0$8 := x$8 ;
		    assume $ReadObject($h_0$8, x$8);
		    y_0$8 := y$8 ;
		    assume $ReadObject($h_0$8, y$8);
		    if(true )
		    {
		    	$t#0_0$8 := $a#0_0$8 ;
		    	assume $ReadObject($h_0$8, $a#0_0$8);
		    }
		    if(true )
		    {
		    	xn_0$8 := $t#0_0$8 ;
		    	assume $ReadObject($h_0$8, $t#0_0$8);
		    }
		    if(true )
		    {
		    	$h_0$8:=$Write($h_0$8,x_0$8,$field#v,xn_0$8); assume $GoodHeap($h_0$8);
		    }
		    if(true )
		    {
		    	$t#1_0$8 := $a#1_0$8 ;
		    	assume $ReadObject($h_0$8, $a#1_0$8);
		    }
		    if(true )
		    {
		    	yn_0$8 := $t#1_0$8 ;
		    	assume $ReadObject($h_0$8, $t#1_0$8);
		    }
		    if(true )
		    {
		    	$h_0$8:=$Write($h_0$8,y_0$8,$field#v,yn_0$8); assume $GoodHeap($h_0$8);
		    }
		    if(true )
		    {
		    	$t#2_0$8 := $a#2_0$8 ;
		    	assume $ReadObject($h_0$8, $a#2_0$8);
		    }
		    if(true )
		    {
		    	n_0$8 := $t#2_0$8 ;
		    	assume $ReadObject($h_0$8, $t#2_0$8);
		    }
		    if(true )
		    {
		    	$h_0$8:=$Write($h_0$8,yn_0$8,$field#v,n_0$8); assume $GoodHeap($h_0$8);
		    }
		    if(true )
		    {
		    	$h_0$8:=$Write($h_0$8,xn_0$8,$field#v,n_0$8); assume $GoodHeap($h_0$8);
		    }

		    // procedure body _1 start
		    x_1$8 := x$8 ;
		    assume $ReadObject($h_1$8, x$8);
		    y_1$8 := y$8 ;
		    assume $ReadObject($h_1$8, y$8);
		    if(true )
		    {
		    	$t#0_1$8 := $a#0_1$8 ;
		    	assume $ReadObject($h_1$8, $a#0_1$8);
		    }
		    if(true )
		    {
		    	xn_1$8 := $t#0_1$8 ;
		    	assume $ReadObject($h_1$8, $t#0_1$8);
		    }
		    if(true )
		    {
		    	$h_1$8:=$Write($h_1$8,x_1$8,$field#v,xn_1$8); assume $GoodHeap($h_1$8);
		    }
		    if(true )
		    {
		    	$t#1_1$8 := $a#1_1$8 ;
		    	assume $ReadObject($h_1$8, $a#1_1$8);
		    }
		    if(true )
		    {
		    	yn_1$8 := $t#1_1$8 ;
		    	assume $ReadObject($h_1$8, $t#1_1$8);
		    }
		    if(true )
		    {
		    	$h_1$8:=$Write($h_1$8,y_1$8,$field#v,yn_1$8); assume $GoodHeap($h_1$8);
		    }
		    if(true )
		    {
		    	$t#2_1$8 := $a#2_1$8 ;
		    	assume $ReadObject($h_1$8, $a#2_1$8);
		    }
		    if(true )
		    {
		    	xnn_1$8 := $t#2_1$8 ;
		    	assume $ReadObject($h_1$8, $t#2_1$8);
		    }
		    if(true )
		    {
		    	$t#3_1$8 := $a#3_1$8 ;
		    	assume $ReadObject($h_1$8, $a#3_1$8);
		    }
		    if(true )
		    {
		    	ynn_1$8 := $t#3_1$8 ;
		    	assume $ReadObject($h_1$8, $t#3_1$8);
		    }
		    if(true )
		    {
		    	$h_1$8:=$Write($h_1$8,yn_1$8,$field#v,ynn_1$8); assume $GoodHeap($h_1$8);
		    }
		    if(true )
		    {
		    	$h_1$8:=$Write($h_1$8,xn_1$8,$field#v,xnn_1$8); assume $GoodHeap($h_1$8);
		    }

		    // restore heaps
		    $h_0$9 := $h;
		    $h_1$9 := $h;

		    x$9 := x;
		    y$9 := y;

		    // prefix start
			havoc $a#0_0$9; assume !$Allocated($h_0$9,$a#0_0$9);
			$h_0$9:=$Allocate($h_0$9,$a#0_0$9); assume $GoodHeap($h_0$9);
			assume $AllocatedObject($h_0$9, $a#0_0$9);
			assert $FieldsNull($h_0$9, $a#0_0$9);
			assert $ReachNull($h_0$9, $a#0_0$9);
			havoc $a#1_0$9; assume !$Allocated($h_0$9,$a#1_0$9);
			$h_0$9:=$Allocate($h_0$9,$a#1_0$9); assume $GoodHeap($h_0$9);
			assume $AllocatedObject($h_0$9, $a#1_0$9);
			assert $FieldsNull($h_0$9, $a#1_0$9);
			assert $ReachNull($h_0$9, $a#1_0$9);
			havoc $a#2_0$9; assume !$Allocated($h_0$9,$a#2_0$9);
			$h_0$9:=$Allocate($h_0$9,$a#2_0$9); assume $GoodHeap($h_0$9);
			assume $AllocatedObject($h_0$9, $a#2_0$9);
			assert $FieldsNull($h_0$9, $a#2_0$9);
			assert $ReachNull($h_0$9, $a#2_0$9);
			havoc $a#3_0$9; assume !$Allocated($h_0$9,$a#3_0$9);
			$h_0$9:=$Allocate($h_0$9,$a#3_0$9); assume $GoodHeap($h_0$9);
			assume $AllocatedObject($h_0$9, $a#3_0$9);
			assert $FieldsNull($h_0$9, $a#3_0$9);
			assert $ReachNull($h_0$9, $a#3_0$9);
			havoc $a#0_1$9; assume !$Allocated($h_1$9,$a#0_1$9);
			$h_1$9:=$Allocate($h_1$9,$a#0_1$9); assume $GoodHeap($h_1$9);
			assume $AllocatedObject($h_1$9, $a#0_1$9);
			assert $FieldsNull($h_1$9, $a#0_1$9);
			assert $ReachNull($h_1$9, $a#0_1$9);
			havoc $a#1_1$9; assume !$Allocated($h_1$9,$a#1_1$9);
			$h_1$9:=$Allocate($h_1$9,$a#1_1$9); assume $GoodHeap($h_1$9);
			assume $AllocatedObject($h_1$9, $a#1_1$9);
			assert $FieldsNull($h_1$9, $a#1_1$9);
			assert $ReachNull($h_1$9, $a#1_1$9);
			havoc $a#2_1$9; assume !$Allocated($h_1$9,$a#2_1$9);
			$h_1$9:=$Allocate($h_1$9,$a#2_1$9); assume $GoodHeap($h_1$9);
			assume $AllocatedObject($h_1$9, $a#2_1$9);
			assert $FieldsNull($h_1$9, $a#2_1$9);
			assert $ReachNull($h_1$9, $a#2_1$9);
			havoc $a#3_1$9; assume !$Allocated($h_1$9,$a#3_1$9);
			$h_1$9:=$Allocate($h_1$9,$a#3_1$9); assume $GoodHeap($h_1$9);
			assume $AllocatedObject($h_1$9, $a#3_1$9);
			assert $FieldsNull($h_1$9, $a#3_1$9);
			assert $ReachNull($h_1$9, $a#3_1$9);

			// assert (forall $a:Ref :: $ReachableFromParams#1($h_0$0, $a#0_0$0, $a) ==> $a==$Null);

				assume $a#3_0$9 == $a#0_1$9;
				assume $a#0_0$9 == $a#1_1$9;
				assume $a#1_0$9 == $a#2_1$9;
				assume $a#2_0$9 == $a#3_1$9;

			// procedure body _0 start	
		    x_0$9 := x$9 ;
		    assume $ReadObject($h_0$9, x$9);
		    y_0$9 := y$9 ;
		    assume $ReadObject($h_0$9, y$9);
		    if(true )
		    {
		    	$t#0_0$9 := $a#0_0$9 ;
		    	assume $ReadObject($h_0$9, $a#0_0$9);
		    }
		    if(true )
		    {
		    	xn_0$9 := $t#0_0$9 ;
		    	assume $ReadObject($h_0$9, $t#0_0$9);
		    }
		    if(true )
		    {
		    	$h_0$9:=$Write($h_0$9,x_0$9,$field#v,xn_0$9); assume $GoodHeap($h_0$9);
		    }
		    if(true )
		    {
		    	$t#1_0$9 := $a#1_0$9 ;
		    	assume $ReadObject($h_0$9, $a#1_0$9);
		    }
		    if(true )
		    {
		    	yn_0$9 := $t#1_0$9 ;
		    	assume $ReadObject($h_0$9, $t#1_0$9);
		    }
		    if(true )
		    {
		    	$h_0$9:=$Write($h_0$9,y_0$9,$field#v,yn_0$9); assume $GoodHeap($h_0$9);
		    }
		    if(true )
		    {
		    	$t#2_0$9 := $a#2_0$9 ;
		    	assume $ReadObject($h_0$9, $a#2_0$9);
		    }
		    if(true )
		    {
		    	n_0$9 := $t#2_0$9 ;
		    	assume $ReadObject($h_0$9, $t#2_0$9);
		    }
		    if(true )
		    {
		    	$h_0$9:=$Write($h_0$9,yn_0$9,$field#v,n_0$9); assume $GoodHeap($h_0$9);
		    }
		    if(true )
		    {
		    	$h_0$9:=$Write($h_0$9,xn_0$9,$field#v,n_0$9); assume $GoodHeap($h_0$9);
		    }

		    // procedure body _1 start
		    x_1$9 := x$9 ;
		    assume $ReadObject($h_1$9, x$9);
		    y_1$9 := y$9 ;
		    assume $ReadObject($h_1$9, y$9);
		    if(true )
		    {
		    	$t#0_1$9 := $a#0_1$9 ;
		    	assume $ReadObject($h_1$9, $a#0_1$9);
		    }
		    if(true )
		    {
		    	xn_1$9 := $t#0_1$9 ;
		    	assume $ReadObject($h_1$9, $t#0_1$9);
		    }
		    if(true )
		    {
		    	$h_1$9:=$Write($h_1$9,x_1$9,$field#v,xn_1$9); assume $GoodHeap($h_1$9);
		    }
		    if(true )
		    {
		    	$t#1_1$9 := $a#1_1$9 ;
		    	assume $ReadObject($h_1$9, $a#1_1$9);
		    }
		    if(true )
		    {
		    	yn_1$9 := $t#1_1$9 ;
		    	assume $ReadObject($h_1$9, $t#1_1$9);
		    }
		    if(true )
		    {
		    	$h_1$9:=$Write($h_1$9,y_1$9,$field#v,yn_1$9); assume $GoodHeap($h_1$9);
		    }
		    if(true )
		    {
		    	$t#2_1$9 := $a#2_1$9 ;
		    	assume $ReadObject($h_1$9, $a#2_1$9);
		    }
		    if(true )
		    {
		    	xnn_1$9 := $t#2_1$9 ;
		    	assume $ReadObject($h_1$9, $t#2_1$9);
		    }
		    if(true )
		    {
		    	$t#3_1$9 := $a#3_1$9 ;
		    	assume $ReadObject($h_1$9, $a#3_1$9);
		    }
		    if(true )
		    {
		    	ynn_1$9 := $t#3_1$9 ;
		    	assume $ReadObject($h_1$9, $t#3_1$9);
		    }
		    if(true )
		    {
		    	$h_1$9:=$Write($h_1$9,yn_1$9,$field#v,ynn_1$9); assume $GoodHeap($h_1$9);
		    }
		    if(true )
		    {
		    	$h_1$9:=$Write($h_1$9,xn_1$9,$field#v,xnn_1$9); assume $GoodHeap($h_1$9);
		    }

		    // restore heaps
		    $h_0$10 := $h;
		    $h_1$10 := $h;

		    x$10 := x;
		    y$10 := y;

		    // prefix start
			havoc $a#0_0$10; assume !$Allocated($h_0$10,$a#0_0$10);
			$h_0$10:=$Allocate($h_0$10,$a#0_0$10); assume $GoodHeap($h_0$10);
			assume $AllocatedObject($h_0$10, $a#0_0$10);
			assert $FieldsNull($h_0$10, $a#0_0$10);
			assert $ReachNull($h_0$10, $a#0_0$10);
			havoc $a#1_0$10; assume !$Allocated($h_0$10,$a#1_0$10);
			$h_0$10:=$Allocate($h_0$10,$a#1_0$10); assume $GoodHeap($h_0$10);
			assume $AllocatedObject($h_0$10, $a#1_0$10);
			assert $FieldsNull($h_0$10, $a#1_0$10);
			assert $ReachNull($h_0$10, $a#1_0$10);
			havoc $a#2_0$10; assume !$Allocated($h_0$10,$a#2_0$10);
			$h_0$10:=$Allocate($h_0$10,$a#2_0$10); assume $GoodHeap($h_0$10);
			assume $AllocatedObject($h_0$10, $a#2_0$10);
			assert $FieldsNull($h_0$10, $a#2_0$10);
			assert $ReachNull($h_0$10, $a#2_0$10);
			havoc $a#3_0$10; assume !$Allocated($h_0$10,$a#3_0$10);
			$h_0$10:=$Allocate($h_0$10,$a#3_0$10); assume $GoodHeap($h_0$10);
			assume $AllocatedObject($h_0$10, $a#3_0$10);
			assert $FieldsNull($h_0$10, $a#3_0$10);
			assert $ReachNull($h_0$10, $a#3_0$10);
			havoc $a#0_1$10; assume !$Allocated($h_1$10,$a#0_1$10);
			$h_1$10:=$Allocate($h_1$10,$a#0_1$10); assume $GoodHeap($h_1$10);
			assume $AllocatedObject($h_1$10, $a#0_1$10);
			assert $FieldsNull($h_1$10, $a#0_1$10);
			assert $ReachNull($h_1$10, $a#0_1$10);
			havoc $a#1_1$10; assume !$Allocated($h_1$10,$a#1_1$10);
			$h_1$10:=$Allocate($h_1$10,$a#1_1$10); assume $GoodHeap($h_1$10);
			assume $AllocatedObject($h_1$10, $a#1_1$10);
			assert $FieldsNull($h_1$10, $a#1_1$10);
			assert $ReachNull($h_1$10, $a#1_1$10);
			havoc $a#2_1$10; assume !$Allocated($h_1$10,$a#2_1$10);
			$h_1$10:=$Allocate($h_1$10,$a#2_1$10); assume $GoodHeap($h_1$10);
			assume $AllocatedObject($h_1$10, $a#2_1$10);
			assert $FieldsNull($h_1$10, $a#2_1$10);
			assert $ReachNull($h_1$10, $a#2_1$10);
			havoc $a#3_1$10; assume !$Allocated($h_1$10,$a#3_1$10);
			$h_1$10:=$Allocate($h_1$10,$a#3_1$10); assume $GoodHeap($h_1$10);
			assume $AllocatedObject($h_1$10, $a#3_1$10);
			assert $FieldsNull($h_1$10, $a#3_1$10);
			assert $ReachNull($h_1$10, $a#3_1$10);

			// assert (forall $a:Ref :: $ReachableFromParams#1($h_0$0, $a#0_0$0, $a) ==> $a==$Null);

				assume $a#1_0$10 == $a#0_1$10;
				assume $a#0_0$10 == $a#1_1$10;
				assume $a#3_0$10 == $a#2_1$10;
				assume $a#2_0$10 == $a#3_1$10;

			// procedure body _0 start	
		    x_0$10 := x$10 ;
		    assume $ReadObject($h_0$10, x$10);
		    y_0$10 := y$10 ;
		    assume $ReadObject($h_0$10, y$10);
		    if(true )
		    {
		    	$t#0_0$10 := $a#0_0$10 ;
		    	assume $ReadObject($h_0$10, $a#0_0$10);
		    }
		    if(true )
		    {
		    	xn_0$10 := $t#0_0$10 ;
		    	assume $ReadObject($h_0$10, $t#0_0$10);
		    }
		    if(true )
		    {
		    	$h_0$10:=$Write($h_0$10,x_0$10,$field#v,xn_0$10); assume $GoodHeap($h_0$10);
		    }
		    if(true )
		    {
		    	$t#1_0$10 := $a#1_0$10 ;
		    	assume $ReadObject($h_0$10, $a#1_0$10);
		    }
		    if(true )
		    {
		    	yn_0$10 := $t#1_0$10 ;
		    	assume $ReadObject($h_0$10, $t#1_0$10);
		    }
		    if(true )
		    {
		    	$h_0$10:=$Write($h_0$10,y_0$10,$field#v,yn_0$10); assume $GoodHeap($h_0$10);
		    }
		    if(true )
		    {
		    	$t#2_0$10 := $a#2_0$10 ;
		    	assume $ReadObject($h_0$10, $a#2_0$10);
		    }
		    if(true )
		    {
		    	n_0$10 := $t#2_0$10 ;
		    	assume $ReadObject($h_0$10, $t#2_0$10);
		    }
		    if(true )
		    {
		    	$h_0$10:=$Write($h_0$10,yn_0$10,$field#v,n_0$10); assume $GoodHeap($h_0$10);
		    }
		    if(true )
		    {
		    	$h_0$10:=$Write($h_0$10,xn_0$10,$field#v,n_0$10); assume $GoodHeap($h_0$10);
		    }

		    // procedure body _1 start
		    x_1$10 := x$10 ;
		    assume $ReadObject($h_1$10, x$10);
		    y_1$10 := y$10 ;
		    assume $ReadObject($h_1$10, y$10);
		    if(true )
		    {
		    	$t#0_1$10 := $a#0_1$10 ;
		    	assume $ReadObject($h_1$10, $a#0_1$10);
		    }
		    if(true )
		    {
		    	xn_1$10 := $t#0_1$10 ;
		    	assume $ReadObject($h_1$10, $t#0_1$10);
		    }
		    if(true )
		    {
		    	$h_1$10:=$Write($h_1$10,x_1$10,$field#v,xn_1$10); assume $GoodHeap($h_1$10);
		    }
		    if(true )
		    {
		    	$t#1_1$10 := $a#1_1$10 ;
		    	assume $ReadObject($h_1$10, $a#1_1$10);
		    }
		    if(true )
		    {
		    	yn_1$10 := $t#1_1$10 ;
		    	assume $ReadObject($h_1$10, $t#1_1$10);
		    }
		    if(true )
		    {
		    	$h_1$10:=$Write($h_1$10,y_1$10,$field#v,yn_1$10); assume $GoodHeap($h_1$10);
		    }
		    if(true )
		    {
		    	$t#2_1$10 := $a#2_1$10 ;
		    	assume $ReadObject($h_1$10, $a#2_1$10);
		    }
		    if(true )
		    {
		    	xnn_1$10 := $t#2_1$10 ;
		    	assume $ReadObject($h_1$10, $t#2_1$10);
		    }
		    if(true )
		    {
		    	$t#3_1$10 := $a#3_1$10 ;
		    	assume $ReadObject($h_1$10, $a#3_1$10);
		    }
		    if(true )
		    {
		    	ynn_1$10 := $t#3_1$10 ;
		    	assume $ReadObject($h_1$10, $t#3_1$10);
		    }
		    if(true )
		    {
		    	$h_1$10:=$Write($h_1$10,yn_1$10,$field#v,ynn_1$10); assume $GoodHeap($h_1$10);
		    }
		    if(true )
		    {
		    	$h_1$10:=$Write($h_1$10,xn_1$10,$field#v,xnn_1$10); assume $GoodHeap($h_1$10);
		    }

		    // restore heaps
		    $h_0$11 := $h;
		    $h_1$11 := $h;

		    x$11 := x;
		    y$11 := y;

		    // prefix start
			havoc $a#0_0$11; assume !$Allocated($h_0$11,$a#0_0$11);
			$h_0$11:=$Allocate($h_0$11,$a#0_0$11); assume $GoodHeap($h_0$11);
			assume $AllocatedObject($h_0$11, $a#0_0$11);
			assert $FieldsNull($h_0$11, $a#0_0$11);
			assert $ReachNull($h_0$11, $a#0_0$11);
			havoc $a#1_0$11; assume !$Allocated($h_0$11,$a#1_0$11);
			$h_0$11:=$Allocate($h_0$11,$a#1_0$11); assume $GoodHeap($h_0$11);
			assume $AllocatedObject($h_0$11, $a#1_0$11);
			assert $FieldsNull($h_0$11, $a#1_0$11);
			assert $ReachNull($h_0$11, $a#1_0$11);
			havoc $a#2_0$11; assume !$Allocated($h_0$11,$a#2_0$11);
			$h_0$11:=$Allocate($h_0$11,$a#2_0$11); assume $GoodHeap($h_0$11);
			assume $AllocatedObject($h_0$11, $a#2_0$11);
			assert $FieldsNull($h_0$11, $a#2_0$11);
			assert $ReachNull($h_0$11, $a#2_0$11);
			havoc $a#3_0$11; assume !$Allocated($h_0$11,$a#3_0$11);
			$h_0$11:=$Allocate($h_0$11,$a#3_0$11); assume $GoodHeap($h_0$11);
			assume $AllocatedObject($h_0$11, $a#3_0$11);
			assert $FieldsNull($h_0$11, $a#3_0$11);
			assert $ReachNull($h_0$11, $a#3_0$11);
			havoc $a#0_1$11; assume !$Allocated($h_1$11,$a#0_1$11);
			$h_1$11:=$Allocate($h_1$11,$a#0_1$11); assume $GoodHeap($h_1$11);
			assume $AllocatedObject($h_1$11, $a#0_1$11);
			assert $FieldsNull($h_1$11, $a#0_1$11);
			assert $ReachNull($h_1$11, $a#0_1$11);
			havoc $a#1_1$11; assume !$Allocated($h_1$11,$a#1_1$11);
			$h_1$11:=$Allocate($h_1$11,$a#1_1$11); assume $GoodHeap($h_1$11);
			assume $AllocatedObject($h_1$11, $a#1_1$11);
			assert $FieldsNull($h_1$11, $a#1_1$11);
			assert $ReachNull($h_1$11, $a#1_1$11);
			havoc $a#2_1$11; assume !$Allocated($h_1$11,$a#2_1$11);
			$h_1$11:=$Allocate($h_1$11,$a#2_1$11); assume $GoodHeap($h_1$11);
			assume $AllocatedObject($h_1$11, $a#2_1$11);
			assert $FieldsNull($h_1$11, $a#2_1$11);
			assert $ReachNull($h_1$11, $a#2_1$11);
			havoc $a#3_1$11; assume !$Allocated($h_1$11,$a#3_1$11);
			$h_1$11:=$Allocate($h_1$11,$a#3_1$11); assume $GoodHeap($h_1$11);
			assume $AllocatedObject($h_1$11, $a#3_1$11);
			assert $FieldsNull($h_1$11, $a#3_1$11);
			assert $ReachNull($h_1$11, $a#3_1$11);

			// assert (forall $a:Ref :: $ReachableFromParams#1($h_0$0, $a#0_0$0, $a) ==> $a==$Null);

				assume $a#0_0$11 == $a#0_1$11;
				assume $a#1_0$11 == $a#1_1$11;
				assume $a#3_0$11 == $a#2_1$11;
				assume $a#2_0$11 == $a#3_1$11;

			// procedure body _0 start	
		    x_0$11 := x$11 ;
		    assume $ReadObject($h_0$11, x$11);
		    y_0$11 := y$11 ;
		    assume $ReadObject($h_0$11, y$11);
		    if(true )
		    {
		    	$t#0_0$11 := $a#0_0$11 ;
		    	assume $ReadObject($h_0$11, $a#0_0$11);
		    }
		    if(true )
		    {
		    	xn_0$11 := $t#0_0$11 ;
		    	assume $ReadObject($h_0$11, $t#0_0$11);
		    }
		    if(true )
		    {
		    	$h_0$11:=$Write($h_0$11,x_0$11,$field#v,xn_0$11); assume $GoodHeap($h_0$11);
		    }
		    if(true )
		    {
		    	$t#1_0$11 := $a#1_0$11 ;
		    	assume $ReadObject($h_0$11, $a#1_0$11);
		    }
		    if(true )
		    {
		    	yn_0$11 := $t#1_0$11 ;
		    	assume $ReadObject($h_0$11, $t#1_0$11);
		    }
		    if(true )
		    {
		    	$h_0$11:=$Write($h_0$11,y_0$11,$field#v,yn_0$11); assume $GoodHeap($h_0$11);
		    }
		    if(true )
		    {
		    	$t#2_0$11 := $a#2_0$11 ;
		    	assume $ReadObject($h_0$11, $a#2_0$11);
		    }
		    if(true )
		    {
		    	n_0$11 := $t#2_0$11 ;
		    	assume $ReadObject($h_0$11, $t#2_0$11);
		    }
		    if(true )
		    {
		    	$h_0$11:=$Write($h_0$11,yn_0$11,$field#v,n_0$11); assume $GoodHeap($h_0$11);
		    }
		    if(true )
		    {
		    	$h_0$11:=$Write($h_0$11,xn_0$11,$field#v,n_0$11); assume $GoodHeap($h_0$11);
		    }

		    // procedure body _1 start
		    x_1$11 := x$11 ;
		    assume $ReadObject($h_1$11, x$11);
		    y_1$11 := y$11 ;
		    assume $ReadObject($h_1$11, y$11);
		    if(true )
		    {
		    	$t#0_1$11 := $a#0_1$11 ;
		    	assume $ReadObject($h_1$11, $a#0_1$11);
		    }
		    if(true )
		    {
		    	xn_1$11 := $t#0_1$11 ;
		    	assume $ReadObject($h_1$11, $t#0_1$11);
		    }
		    if(true )
		    {
		    	$h_1$11:=$Write($h_1$11,x_1$11,$field#v,xn_1$11); assume $GoodHeap($h_1$11);
		    }
		    if(true )
		    {
		    	$t#1_1$11 := $a#1_1$11 ;
		    	assume $ReadObject($h_1$11, $a#1_1$11);
		    }
		    if(true )
		    {
		    	yn_1$11 := $t#1_1$11 ;
		    	assume $ReadObject($h_1$11, $t#1_1$11);
		    }
		    if(true )
		    {
		    	$h_1$11:=$Write($h_1$11,y_1$11,$field#v,yn_1$11); assume $GoodHeap($h_1$11);
		    }
		    if(true )
		    {
		    	$t#2_1$11 := $a#2_1$11 ;
		    	assume $ReadObject($h_1$11, $a#2_1$11);
		    }
		    if(true )
		    {
		    	xnn_1$11 := $t#2_1$11 ;
		    	assume $ReadObject($h_1$11, $t#2_1$11);
		    }
		    if(true )
		    {
		    	$t#3_1$11 := $a#3_1$11 ;
		    	assume $ReadObject($h_1$11, $a#3_1$11);
		    }
		    if(true )
		    {
		    	ynn_1$11 := $t#3_1$11 ;
		    	assume $ReadObject($h_1$11, $t#3_1$11);
		    }
		    if(true )
		    {
		    	$h_1$11:=$Write($h_1$11,yn_1$11,$field#v,ynn_1$11); assume $GoodHeap($h_1$11);
		    }
		    if(true )
		    {
		    	$h_1$11:=$Write($h_1$11,xn_1$11,$field#v,xnn_1$11); assume $GoodHeap($h_1$11);
		    }

		    // restore heaps
		    $h_0$12 := $h;
		    $h_1$12 := $h;

		    x$12 := x;
		    y$12 := y;

		    // prefix start
			havoc $a#0_0$12; assume !$Allocated($h_0$12,$a#0_0$12);
			$h_0$12:=$Allocate($h_0$12,$a#0_0$12); assume $GoodHeap($h_0$12);
			assume $AllocatedObject($h_0$12, $a#0_0$12);
			assert $FieldsNull($h_0$12, $a#0_0$12);
			assert $ReachNull($h_0$12, $a#0_0$12);
			havoc $a#1_0$12; assume !$Allocated($h_0$12,$a#1_0$12);
			$h_0$12:=$Allocate($h_0$12,$a#1_0$12); assume $GoodHeap($h_0$12);
			assume $AllocatedObject($h_0$12, $a#1_0$12);
			assert $FieldsNull($h_0$12, $a#1_0$12);
			assert $ReachNull($h_0$12, $a#1_0$12);
			havoc $a#2_0$12; assume !$Allocated($h_0$12,$a#2_0$12);
			$h_0$12:=$Allocate($h_0$12,$a#2_0$12); assume $GoodHeap($h_0$12);
			assume $AllocatedObject($h_0$12, $a#2_0$12);
			assert $FieldsNull($h_0$12, $a#2_0$12);
			assert $ReachNull($h_0$12, $a#2_0$12);
			havoc $a#3_0$12; assume !$Allocated($h_0$12,$a#3_0$12);
			$h_0$12:=$Allocate($h_0$12,$a#3_0$12); assume $GoodHeap($h_0$12);
			assume $AllocatedObject($h_0$12, $a#3_0$12);
			assert $FieldsNull($h_0$12, $a#3_0$12);
			assert $ReachNull($h_0$12, $a#3_0$12);
			havoc $a#0_1$12; assume !$Allocated($h_1$12,$a#0_1$12);
			$h_1$12:=$Allocate($h_1$12,$a#0_1$12); assume $GoodHeap($h_1$12);
			assume $AllocatedObject($h_1$12, $a#0_1$12);
			assert $FieldsNull($h_1$12, $a#0_1$12);
			assert $ReachNull($h_1$12, $a#0_1$12);
			havoc $a#1_1$12; assume !$Allocated($h_1$12,$a#1_1$12);
			$h_1$12:=$Allocate($h_1$12,$a#1_1$12); assume $GoodHeap($h_1$12);
			assume $AllocatedObject($h_1$12, $a#1_1$12);
			assert $FieldsNull($h_1$12, $a#1_1$12);
			assert $ReachNull($h_1$12, $a#1_1$12);
			havoc $a#2_1$12; assume !$Allocated($h_1$12,$a#2_1$12);
			$h_1$12:=$Allocate($h_1$12,$a#2_1$12); assume $GoodHeap($h_1$12);
			assume $AllocatedObject($h_1$12, $a#2_1$12);
			assert $FieldsNull($h_1$12, $a#2_1$12);
			assert $ReachNull($h_1$12, $a#2_1$12);
			havoc $a#3_1$12; assume !$Allocated($h_1$12,$a#3_1$12);
			$h_1$12:=$Allocate($h_1$12,$a#3_1$12); assume $GoodHeap($h_1$12);
			assume $AllocatedObject($h_1$12, $a#3_1$12);
			assert $FieldsNull($h_1$12, $a#3_1$12);
			assert $ReachNull($h_1$12, $a#3_1$12);

			// assert (forall $a:Ref :: $ReachableFromParams#1($h_0$0, $a#0_0$0, $a) ==> $a==$Null);

				assume $a#0_0$12 == $a#0_1$12;
				assume $a#2_0$12 == $a#1_1$12;
				assume $a#3_0$12 == $a#2_1$12;
				assume $a#1_0$12 == $a#3_1$12;

			// procedure body _0 start	
		    x_0$12 := x$12 ;
		    assume $ReadObject($h_0$12, x$12);
		    y_0$12 := y$12 ;
		    assume $ReadObject($h_0$12, y$12);
		    if(true )
		    {
		    	$t#0_0$12 := $a#0_0$12 ;
		    	assume $ReadObject($h_0$12, $a#0_0$12);
		    }
		    if(true )
		    {
		    	xn_0$12 := $t#0_0$12 ;
		    	assume $ReadObject($h_0$12, $t#0_0$12);
		    }
		    if(true )
		    {
		    	$h_0$12:=$Write($h_0$12,x_0$12,$field#v,xn_0$12); assume $GoodHeap($h_0$12);
		    }
		    if(true )
		    {
		    	$t#1_0$12 := $a#1_0$12 ;
		    	assume $ReadObject($h_0$12, $a#1_0$12);
		    }
		    if(true )
		    {
		    	yn_0$12 := $t#1_0$12 ;
		    	assume $ReadObject($h_0$12, $t#1_0$12);
		    }
		    if(true )
		    {
		    	$h_0$12:=$Write($h_0$12,y_0$12,$field#v,yn_0$12); assume $GoodHeap($h_0$12);
		    }
		    if(true )
		    {
		    	$t#2_0$12 := $a#2_0$12 ;
		    	assume $ReadObject($h_0$12, $a#2_0$12);
		    }
		    if(true )
		    {
		    	n_0$12 := $t#2_0$12 ;
		    	assume $ReadObject($h_0$12, $t#2_0$12);
		    }
		    if(true )
		    {
		    	$h_0$12:=$Write($h_0$12,yn_0$12,$field#v,n_0$12); assume $GoodHeap($h_0$12);
		    }
		    if(true )
		    {
		    	$h_0$12:=$Write($h_0$12,xn_0$12,$field#v,n_0$12); assume $GoodHeap($h_0$12);
		    }

		    // procedure body _1 start
		    x_1$12 := x$12 ;
		    assume $ReadObject($h_1$12, x$12);
		    y_1$12 := y$12 ;
		    assume $ReadObject($h_1$12, y$12);
		    if(true )
		    {
		    	$t#0_1$12 := $a#0_1$12 ;
		    	assume $ReadObject($h_1$12, $a#0_1$12);
		    }
		    if(true )
		    {
		    	xn_1$12 := $t#0_1$12 ;
		    	assume $ReadObject($h_1$12, $t#0_1$12);
		    }
		    if(true )
		    {
		    	$h_1$12:=$Write($h_1$12,x_1$12,$field#v,xn_1$12); assume $GoodHeap($h_1$12);
		    }
		    if(true )
		    {
		    	$t#1_1$12 := $a#1_1$12 ;
		    	assume $ReadObject($h_1$12, $a#1_1$12);
		    }
		    if(true )
		    {
		    	yn_1$12 := $t#1_1$12 ;
		    	assume $ReadObject($h_1$12, $t#1_1$12);
		    }
		    if(true )
		    {
		    	$h_1$12:=$Write($h_1$12,y_1$12,$field#v,yn_1$12); assume $GoodHeap($h_1$12);
		    }
		    if(true )
		    {
		    	$t#2_1$12 := $a#2_1$12 ;
		    	assume $ReadObject($h_1$12, $a#2_1$12);
		    }
		    if(true )
		    {
		    	xnn_1$12 := $t#2_1$12 ;
		    	assume $ReadObject($h_1$12, $t#2_1$12);
		    }
		    if(true )
		    {
		    	$t#3_1$12 := $a#3_1$12 ;
		    	assume $ReadObject($h_1$12, $a#3_1$12);
		    }
		    if(true )
		    {
		    	ynn_1$12 := $t#3_1$12 ;
		    	assume $ReadObject($h_1$12, $t#3_1$12);
		    }
		    if(true )
		    {
		    	$h_1$12:=$Write($h_1$12,yn_1$12,$field#v,ynn_1$12); assume $GoodHeap($h_1$12);
		    }
		    if(true )
		    {
		    	$h_1$12:=$Write($h_1$12,xn_1$12,$field#v,xnn_1$12); assume $GoodHeap($h_1$12);
		    }

		    // restore heaps
		    $h_0$13 := $h;
		    $h_1$13 := $h;

		    x$13 := x;
		    y$13 := y;

		    // prefix start
			havoc $a#0_0$13; assume !$Allocated($h_0$13,$a#0_0$13);
			$h_0$13:=$Allocate($h_0$13,$a#0_0$13); assume $GoodHeap($h_0$13);
			assume $AllocatedObject($h_0$13, $a#0_0$13);
			assert $FieldsNull($h_0$13, $a#0_0$13);
			assert $ReachNull($h_0$13, $a#0_0$13);
			havoc $a#1_0$13; assume !$Allocated($h_0$13,$a#1_0$13);
			$h_0$13:=$Allocate($h_0$13,$a#1_0$13); assume $GoodHeap($h_0$13);
			assume $AllocatedObject($h_0$13, $a#1_0$13);
			assert $FieldsNull($h_0$13, $a#1_0$13);
			assert $ReachNull($h_0$13, $a#1_0$13);
			havoc $a#2_0$13; assume !$Allocated($h_0$13,$a#2_0$13);
			$h_0$13:=$Allocate($h_0$13,$a#2_0$13); assume $GoodHeap($h_0$13);
			assume $AllocatedObject($h_0$13, $a#2_0$13);
			assert $FieldsNull($h_0$13, $a#2_0$13);
			assert $ReachNull($h_0$13, $a#2_0$13);
			havoc $a#3_0$13; assume !$Allocated($h_0$13,$a#3_0$13);
			$h_0$13:=$Allocate($h_0$13,$a#3_0$13); assume $GoodHeap($h_0$13);
			assume $AllocatedObject($h_0$13, $a#3_0$13);
			assert $FieldsNull($h_0$13, $a#3_0$13);
			assert $ReachNull($h_0$13, $a#3_0$13);
			havoc $a#0_1$13; assume !$Allocated($h_1$13,$a#0_1$13);
			$h_1$13:=$Allocate($h_1$13,$a#0_1$13); assume $GoodHeap($h_1$13);
			assume $AllocatedObject($h_1$13, $a#0_1$13);
			assert $FieldsNull($h_1$13, $a#0_1$13);
			assert $ReachNull($h_1$13, $a#0_1$13);
			havoc $a#1_1$13; assume !$Allocated($h_1$13,$a#1_1$13);
			$h_1$13:=$Allocate($h_1$13,$a#1_1$13); assume $GoodHeap($h_1$13);
			assume $AllocatedObject($h_1$13, $a#1_1$13);
			assert $FieldsNull($h_1$13, $a#1_1$13);
			assert $ReachNull($h_1$13, $a#1_1$13);
			havoc $a#2_1$13; assume !$Allocated($h_1$13,$a#2_1$13);
			$h_1$13:=$Allocate($h_1$13,$a#2_1$13); assume $GoodHeap($h_1$13);
			assume $AllocatedObject($h_1$13, $a#2_1$13);
			assert $FieldsNull($h_1$13, $a#2_1$13);
			assert $ReachNull($h_1$13, $a#2_1$13);
			havoc $a#3_1$13; assume !$Allocated($h_1$13,$a#3_1$13);
			$h_1$13:=$Allocate($h_1$13,$a#3_1$13); assume $GoodHeap($h_1$13);
			assume $AllocatedObject($h_1$13, $a#3_1$13);
			assert $FieldsNull($h_1$13, $a#3_1$13);
			assert $ReachNull($h_1$13, $a#3_1$13);

			// assert (forall $a:Ref :: $ReachableFromParams#1($h_0$0, $a#0_0$0, $a) ==> $a==$Null);

				assume $a#2_0$13 == $a#0_1$13;
				assume $a#0_0$13 == $a#1_1$13;
				assume $a#3_0$13 == $a#2_1$13;
				assume $a#1_0$13 == $a#3_1$13;

			// procedure body _0 start	
		    x_0$13 := x$13 ;
		    assume $ReadObject($h_0$13, x$13);
		    y_0$13 := y$13 ;
		    assume $ReadObject($h_0$13, y$13);
		    if(true )
		    {
		    	$t#0_0$13 := $a#0_0$13 ;
		    	assume $ReadObject($h_0$13, $a#0_0$13);
		    }
		    if(true )
		    {
		    	xn_0$13 := $t#0_0$13 ;
		    	assume $ReadObject($h_0$13, $t#0_0$13);
		    }
		    if(true )
		    {
		    	$h_0$13:=$Write($h_0$13,x_0$13,$field#v,xn_0$13); assume $GoodHeap($h_0$13);
		    }
		    if(true )
		    {
		    	$t#1_0$13 := $a#1_0$13 ;
		    	assume $ReadObject($h_0$13, $a#1_0$13);
		    }
		    if(true )
		    {
		    	yn_0$13 := $t#1_0$13 ;
		    	assume $ReadObject($h_0$13, $t#1_0$13);
		    }
		    if(true )
		    {
		    	$h_0$13:=$Write($h_0$13,y_0$13,$field#v,yn_0$13); assume $GoodHeap($h_0$13);
		    }
		    if(true )
		    {
		    	$t#2_0$13 := $a#2_0$13 ;
		    	assume $ReadObject($h_0$13, $a#2_0$13);
		    }
		    if(true )
		    {
		    	n_0$13 := $t#2_0$13 ;
		    	assume $ReadObject($h_0$13, $t#2_0$13);
		    }
		    if(true )
		    {
		    	$h_0$13:=$Write($h_0$13,yn_0$13,$field#v,n_0$13); assume $GoodHeap($h_0$13);
		    }
		    if(true )
		    {
		    	$h_0$13:=$Write($h_0$13,xn_0$13,$field#v,n_0$13); assume $GoodHeap($h_0$13);
		    }

		    // procedure body _1 start
		    x_1$13 := x$13 ;
		    assume $ReadObject($h_1$13, x$13);
		    y_1$13 := y$13 ;
		    assume $ReadObject($h_1$13, y$13);
		    if(true )
		    {
		    	$t#0_1$13 := $a#0_1$13 ;
		    	assume $ReadObject($h_1$13, $a#0_1$13);
		    }
		    if(true )
		    {
		    	xn_1$13 := $t#0_1$13 ;
		    	assume $ReadObject($h_1$13, $t#0_1$13);
		    }
		    if(true )
		    {
		    	$h_1$13:=$Write($h_1$13,x_1$13,$field#v,xn_1$13); assume $GoodHeap($h_1$13);
		    }
		    if(true )
		    {
		    	$t#1_1$13 := $a#1_1$13 ;
		    	assume $ReadObject($h_1$13, $a#1_1$13);
		    }
		    if(true )
		    {
		    	yn_1$13 := $t#1_1$13 ;
		    	assume $ReadObject($h_1$13, $t#1_1$13);
		    }
		    if(true )
		    {
		    	$h_1$13:=$Write($h_1$13,y_1$13,$field#v,yn_1$13); assume $GoodHeap($h_1$13);
		    }
		    if(true )
		    {
		    	$t#2_1$13 := $a#2_1$13 ;
		    	assume $ReadObject($h_1$13, $a#2_1$13);
		    }
		    if(true )
		    {
		    	xnn_1$13 := $t#2_1$13 ;
		    	assume $ReadObject($h_1$13, $t#2_1$13);
		    }
		    if(true )
		    {
		    	$t#3_1$13 := $a#3_1$13 ;
		    	assume $ReadObject($h_1$13, $a#3_1$13);
		    }
		    if(true )
		    {
		    	ynn_1$13 := $t#3_1$13 ;
		    	assume $ReadObject($h_1$13, $t#3_1$13);
		    }
		    if(true )
		    {
		    	$h_1$13:=$Write($h_1$13,yn_1$13,$field#v,ynn_1$13); assume $GoodHeap($h_1$13);
		    }
		    if(true )
		    {
		    	$h_1$13:=$Write($h_1$13,xn_1$13,$field#v,xnn_1$13); assume $GoodHeap($h_1$13);
		    }

		    // restore heaps
		    $h_0$14 := $h;
		    $h_1$14 := $h;

		    x$14 := x;
		    y$14 := y;

		    // prefix start
			havoc $a#0_0$14; assume !$Allocated($h_0$14,$a#0_0$14);
			$h_0$14:=$Allocate($h_0$14,$a#0_0$14); assume $GoodHeap($h_0$14);
			assume $AllocatedObject($h_0$14, $a#0_0$14);
			assert $FieldsNull($h_0$14, $a#0_0$14);
			assert $ReachNull($h_0$14, $a#0_0$14);
			havoc $a#1_0$14; assume !$Allocated($h_0$14,$a#1_0$14);
			$h_0$14:=$Allocate($h_0$14,$a#1_0$14); assume $GoodHeap($h_0$14);
			assume $AllocatedObject($h_0$14, $a#1_0$14);
			assert $FieldsNull($h_0$14, $a#1_0$14);
			assert $ReachNull($h_0$14, $a#1_0$14);
			havoc $a#2_0$14; assume !$Allocated($h_0$14,$a#2_0$14);
			$h_0$14:=$Allocate($h_0$14,$a#2_0$14); assume $GoodHeap($h_0$14);
			assume $AllocatedObject($h_0$14, $a#2_0$14);
			assert $FieldsNull($h_0$14, $a#2_0$14);
			assert $ReachNull($h_0$14, $a#2_0$14);
			havoc $a#3_0$14; assume !$Allocated($h_0$14,$a#3_0$14);
			$h_0$14:=$Allocate($h_0$14,$a#3_0$14); assume $GoodHeap($h_0$14);
			assume $AllocatedObject($h_0$14, $a#3_0$14);
			assert $FieldsNull($h_0$14, $a#3_0$14);
			assert $ReachNull($h_0$14, $a#3_0$14);
			havoc $a#0_1$14; assume !$Allocated($h_1$14,$a#0_1$14);
			$h_1$14:=$Allocate($h_1$14,$a#0_1$14); assume $GoodHeap($h_1$14);
			assume $AllocatedObject($h_1$14, $a#0_1$14);
			assert $FieldsNull($h_1$14, $a#0_1$14);
			assert $ReachNull($h_1$14, $a#0_1$14);
			havoc $a#1_1$14; assume !$Allocated($h_1$14,$a#1_1$14);
			$h_1$14:=$Allocate($h_1$14,$a#1_1$14); assume $GoodHeap($h_1$14);
			assume $AllocatedObject($h_1$14, $a#1_1$14);
			assert $FieldsNull($h_1$14, $a#1_1$14);
			assert $ReachNull($h_1$14, $a#1_1$14);
			havoc $a#2_1$14; assume !$Allocated($h_1$14,$a#2_1$14);
			$h_1$14:=$Allocate($h_1$14,$a#2_1$14); assume $GoodHeap($h_1$14);
			assume $AllocatedObject($h_1$14, $a#2_1$14);
			assert $FieldsNull($h_1$14, $a#2_1$14);
			assert $ReachNull($h_1$14, $a#2_1$14);
			havoc $a#3_1$14; assume !$Allocated($h_1$14,$a#3_1$14);
			$h_1$14:=$Allocate($h_1$14,$a#3_1$14); assume $GoodHeap($h_1$14);
			assume $AllocatedObject($h_1$14, $a#3_1$14);
			assert $FieldsNull($h_1$14, $a#3_1$14);
			assert $ReachNull($h_1$14, $a#3_1$14);

			// assert (forall $a:Ref :: $ReachableFromParams#1($h_0$0, $a#0_0$0, $a) ==> $a==$Null);

				assume $a#3_0$14 == $a#0_1$14;
				assume $a#0_0$14 == $a#1_1$14;
				assume $a#2_0$14 == $a#2_1$14;
				assume $a#1_0$14 == $a#3_1$14;

			// procedure body _0 start	
		    x_0$14 := x$14 ;
		    assume $ReadObject($h_0$14, x$14);
		    y_0$14 := y$14 ;
		    assume $ReadObject($h_0$14, y$14);
		    if(true )
		    {
		    	$t#0_0$14 := $a#0_0$14 ;
		    	assume $ReadObject($h_0$14, $a#0_0$14);
		    }
		    if(true )
		    {
		    	xn_0$14 := $t#0_0$14 ;
		    	assume $ReadObject($h_0$14, $t#0_0$14);
		    }
		    if(true )
		    {
		    	$h_0$14:=$Write($h_0$14,x_0$14,$field#v,xn_0$14); assume $GoodHeap($h_0$14);
		    }
		    if(true )
		    {
		    	$t#1_0$14 := $a#1_0$14 ;
		    	assume $ReadObject($h_0$14, $a#1_0$14);
		    }
		    if(true )
		    {
		    	yn_0$14 := $t#1_0$14 ;
		    	assume $ReadObject($h_0$14, $t#1_0$14);
		    }
		    if(true )
		    {
		    	$h_0$14:=$Write($h_0$14,y_0$14,$field#v,yn_0$14); assume $GoodHeap($h_0$14);
		    }
		    if(true )
		    {
		    	$t#2_0$14 := $a#2_0$14 ;
		    	assume $ReadObject($h_0$14, $a#2_0$14);
		    }
		    if(true )
		    {
		    	n_0$14 := $t#2_0$14 ;
		    	assume $ReadObject($h_0$14, $t#2_0$14);
		    }
		    if(true )
		    {
		    	$h_0$14:=$Write($h_0$14,yn_0$14,$field#v,n_0$14); assume $GoodHeap($h_0$14);
		    }
		    if(true )
		    {
		    	$h_0$14:=$Write($h_0$14,xn_0$14,$field#v,n_0$14); assume $GoodHeap($h_0$14);
		    }

		    // procedure body _1 start
		    x_1$14 := x$14 ;
		    assume $ReadObject($h_1$14, x$14);
		    y_1$14 := y$14 ;
		    assume $ReadObject($h_1$14, y$14);
		    if(true )
		    {
		    	$t#0_1$14 := $a#0_1$14 ;
		    	assume $ReadObject($h_1$14, $a#0_1$14);
		    }
		    if(true )
		    {
		    	xn_1$14 := $t#0_1$14 ;
		    	assume $ReadObject($h_1$14, $t#0_1$14);
		    }
		    if(true )
		    {
		    	$h_1$14:=$Write($h_1$14,x_1$14,$field#v,xn_1$14); assume $GoodHeap($h_1$14);
		    }
		    if(true )
		    {
		    	$t#1_1$14 := $a#1_1$14 ;
		    	assume $ReadObject($h_1$14, $a#1_1$14);
		    }
		    if(true )
		    {
		    	yn_1$14 := $t#1_1$14 ;
		    	assume $ReadObject($h_1$14, $t#1_1$14);
		    }
		    if(true )
		    {
		    	$h_1$14:=$Write($h_1$14,y_1$14,$field#v,yn_1$14); assume $GoodHeap($h_1$14);
		    }
		    if(true )
		    {
		    	$t#2_1$14 := $a#2_1$14 ;
		    	assume $ReadObject($h_1$14, $a#2_1$14);
		    }
		    if(true )
		    {
		    	xnn_1$14 := $t#2_1$14 ;
		    	assume $ReadObject($h_1$14, $t#2_1$14);
		    }
		    if(true )
		    {
		    	$t#3_1$14 := $a#3_1$14 ;
		    	assume $ReadObject($h_1$14, $a#3_1$14);
		    }
		    if(true )
		    {
		    	ynn_1$14 := $t#3_1$14 ;
		    	assume $ReadObject($h_1$14, $t#3_1$14);
		    }
		    if(true )
		    {
		    	$h_1$14:=$Write($h_1$14,yn_1$14,$field#v,ynn_1$14); assume $GoodHeap($h_1$14);
		    }
		    if(true )
		    {
		    	$h_1$14:=$Write($h_1$14,xn_1$14,$field#v,xnn_1$14); assume $GoodHeap($h_1$14);
		    }

		    // restore heaps
		    $h_0$15 := $h;
		    $h_1$15 := $h;

		    x$15 := x;
		    y$15 := y;

		    // prefix start
			havoc $a#0_0$15; assume !$Allocated($h_0$15,$a#0_0$15);
			$h_0$15:=$Allocate($h_0$15,$a#0_0$15); assume $GoodHeap($h_0$15);
			assume $AllocatedObject($h_0$15, $a#0_0$15);
			assert $FieldsNull($h_0$15, $a#0_0$15);
			assert $ReachNull($h_0$15, $a#0_0$15);
			havoc $a#1_0$15; assume !$Allocated($h_0$15,$a#1_0$15);
			$h_0$15:=$Allocate($h_0$15,$a#1_0$15); assume $GoodHeap($h_0$15);
			assume $AllocatedObject($h_0$15, $a#1_0$15);
			assert $FieldsNull($h_0$15, $a#1_0$15);
			assert $ReachNull($h_0$15, $a#1_0$15);
			havoc $a#2_0$15; assume !$Allocated($h_0$15,$a#2_0$15);
			$h_0$15:=$Allocate($h_0$15,$a#2_0$15); assume $GoodHeap($h_0$15);
			assume $AllocatedObject($h_0$15, $a#2_0$15);
			assert $FieldsNull($h_0$15, $a#2_0$15);
			assert $ReachNull($h_0$15, $a#2_0$15);
			havoc $a#3_0$15; assume !$Allocated($h_0$15,$a#3_0$15);
			$h_0$15:=$Allocate($h_0$15,$a#3_0$15); assume $GoodHeap($h_0$15);
			assume $AllocatedObject($h_0$15, $a#3_0$15);
			assert $FieldsNull($h_0$15, $a#3_0$15);
			assert $ReachNull($h_0$15, $a#3_0$15);
			havoc $a#0_1$15; assume !$Allocated($h_1$15,$a#0_1$15);
			$h_1$15:=$Allocate($h_1$15,$a#0_1$15); assume $GoodHeap($h_1$15);
			assume $AllocatedObject($h_1$15, $a#0_1$15);
			assert $FieldsNull($h_1$15, $a#0_1$15);
			assert $ReachNull($h_1$15, $a#0_1$15);
			havoc $a#1_1$15; assume !$Allocated($h_1$15,$a#1_1$15);
			$h_1$15:=$Allocate($h_1$15,$a#1_1$15); assume $GoodHeap($h_1$15);
			assume $AllocatedObject($h_1$15, $a#1_1$15);
			assert $FieldsNull($h_1$15, $a#1_1$15);
			assert $ReachNull($h_1$15, $a#1_1$15);
			havoc $a#2_1$15; assume !$Allocated($h_1$15,$a#2_1$15);
			$h_1$15:=$Allocate($h_1$15,$a#2_1$15); assume $GoodHeap($h_1$15);
			assume $AllocatedObject($h_1$15, $a#2_1$15);
			assert $FieldsNull($h_1$15, $a#2_1$15);
			assert $ReachNull($h_1$15, $a#2_1$15);
			havoc $a#3_1$15; assume !$Allocated($h_1$15,$a#3_1$15);
			$h_1$15:=$Allocate($h_1$15,$a#3_1$15); assume $GoodHeap($h_1$15);
			assume $AllocatedObject($h_1$15, $a#3_1$15);
			assert $FieldsNull($h_1$15, $a#3_1$15);
			assert $ReachNull($h_1$15, $a#3_1$15);

			// assert (forall $a:Ref :: $ReachableFromParams#1($h_0$0, $a#0_0$0, $a) ==> $a==$Null);

				assume $a#0_0$15 == $a#0_1$15;
				assume $a#3_0$15 == $a#1_1$15;
				assume $a#2_0$15 == $a#2_1$15;
				assume $a#1_0$15 == $a#3_1$15;

			// procedure body _0 start	
		    x_0$15 := x$15 ;
		    assume $ReadObject($h_0$15, x$15);
		    y_0$15 := y$15 ;
		    assume $ReadObject($h_0$15, y$15);
		    if(true )
		    {
		    	$t#0_0$15 := $a#0_0$15 ;
		    	assume $ReadObject($h_0$15, $a#0_0$15);
		    }
		    if(true )
		    {
		    	xn_0$15 := $t#0_0$15 ;
		    	assume $ReadObject($h_0$15, $t#0_0$15);
		    }
		    if(true )
		    {
		    	$h_0$15:=$Write($h_0$15,x_0$15,$field#v,xn_0$15); assume $GoodHeap($h_0$15);
		    }
		    if(true )
		    {
		    	$t#1_0$15 := $a#1_0$15 ;
		    	assume $ReadObject($h_0$15, $a#1_0$15);
		    }
		    if(true )
		    {
		    	yn_0$15 := $t#1_0$15 ;
		    	assume $ReadObject($h_0$15, $t#1_0$15);
		    }
		    if(true )
		    {
		    	$h_0$15:=$Write($h_0$15,y_0$15,$field#v,yn_0$15); assume $GoodHeap($h_0$15);
		    }
		    if(true )
		    {
		    	$t#2_0$15 := $a#2_0$15 ;
		    	assume $ReadObject($h_0$15, $a#2_0$15);
		    }
		    if(true )
		    {
		    	n_0$15 := $t#2_0$15 ;
		    	assume $ReadObject($h_0$15, $t#2_0$15);
		    }
		    if(true )
		    {
		    	$h_0$15:=$Write($h_0$15,yn_0$15,$field#v,n_0$15); assume $GoodHeap($h_0$15);
		    }
		    if(true )
		    {
		    	$h_0$15:=$Write($h_0$15,xn_0$15,$field#v,n_0$15); assume $GoodHeap($h_0$15);
		    }

		    // procedure body _1 start
		    x_1$15 := x$15 ;
		    assume $ReadObject($h_1$15, x$15);
		    y_1$15 := y$15 ;
		    assume $ReadObject($h_1$15, y$15);
		    if(true )
		    {
		    	$t#0_1$15 := $a#0_1$15 ;
		    	assume $ReadObject($h_1$15, $a#0_1$15);
		    }
		    if(true )
		    {
		    	xn_1$15 := $t#0_1$15 ;
		    	assume $ReadObject($h_1$15, $t#0_1$15);
		    }
		    if(true )
		    {
		    	$h_1$15:=$Write($h_1$15,x_1$15,$field#v,xn_1$15); assume $GoodHeap($h_1$15);
		    }
		    if(true )
		    {
		    	$t#1_1$15 := $a#1_1$15 ;
		    	assume $ReadObject($h_1$15, $a#1_1$15);
		    }
		    if(true )
		    {
		    	yn_1$15 := $t#1_1$15 ;
		    	assume $ReadObject($h_1$15, $t#1_1$15);
		    }
		    if(true )
		    {
		    	$h_1$15:=$Write($h_1$15,y_1$15,$field#v,yn_1$15); assume $GoodHeap($h_1$15);
		    }
		    if(true )
		    {
		    	$t#2_1$15 := $a#2_1$15 ;
		    	assume $ReadObject($h_1$15, $a#2_1$15);
		    }
		    if(true )
		    {
		    	xnn_1$15 := $t#2_1$15 ;
		    	assume $ReadObject($h_1$15, $t#2_1$15);
		    }
		    if(true )
		    {
		    	$t#3_1$15 := $a#3_1$15 ;
		    	assume $ReadObject($h_1$15, $a#3_1$15);
		    }
		    if(true )
		    {
		    	ynn_1$15 := $t#3_1$15 ;
		    	assume $ReadObject($h_1$15, $t#3_1$15);
		    }
		    if(true )
		    {
		    	$h_1$15:=$Write($h_1$15,yn_1$15,$field#v,ynn_1$15); assume $GoodHeap($h_1$15);
		    }
		    if(true )
		    {
		    	$h_1$15:=$Write($h_1$15,xn_1$15,$field#v,xnn_1$15); assume $GoodHeap($h_1$15);
		    }

		    // restore heaps
		    $h_0$16 := $h;
		    $h_1$16 := $h;

		    x$16 := x;
		    y$16 := y;

		    // prefix start
			havoc $a#0_0$16; assume !$Allocated($h_0$16,$a#0_0$16);
			$h_0$16:=$Allocate($h_0$16,$a#0_0$16); assume $GoodHeap($h_0$16);
			assume $AllocatedObject($h_0$16, $a#0_0$16);
			assert $FieldsNull($h_0$16, $a#0_0$16);
			assert $ReachNull($h_0$16, $a#0_0$16);
			havoc $a#1_0$16; assume !$Allocated($h_0$16,$a#1_0$16);
			$h_0$16:=$Allocate($h_0$16,$a#1_0$16); assume $GoodHeap($h_0$16);
			assume $AllocatedObject($h_0$16, $a#1_0$16);
			assert $FieldsNull($h_0$16, $a#1_0$16);
			assert $ReachNull($h_0$16, $a#1_0$16);
			havoc $a#2_0$16; assume !$Allocated($h_0$16,$a#2_0$16);
			$h_0$16:=$Allocate($h_0$16,$a#2_0$16); assume $GoodHeap($h_0$16);
			assume $AllocatedObject($h_0$16, $a#2_0$16);
			assert $FieldsNull($h_0$16, $a#2_0$16);
			assert $ReachNull($h_0$16, $a#2_0$16);
			havoc $a#3_0$16; assume !$Allocated($h_0$16,$a#3_0$16);
			$h_0$16:=$Allocate($h_0$16,$a#3_0$16); assume $GoodHeap($h_0$16);
			assume $AllocatedObject($h_0$16, $a#3_0$16);
			assert $FieldsNull($h_0$16, $a#3_0$16);
			assert $ReachNull($h_0$16, $a#3_0$16);
			havoc $a#0_1$16; assume !$Allocated($h_1$16,$a#0_1$16);
			$h_1$16:=$Allocate($h_1$16,$a#0_1$16); assume $GoodHeap($h_1$16);
			assume $AllocatedObject($h_1$16, $a#0_1$16);
			assert $FieldsNull($h_1$16, $a#0_1$16);
			assert $ReachNull($h_1$16, $a#0_1$16);
			havoc $a#1_1$16; assume !$Allocated($h_1$16,$a#1_1$16);
			$h_1$16:=$Allocate($h_1$16,$a#1_1$16); assume $GoodHeap($h_1$16);
			assume $AllocatedObject($h_1$16, $a#1_1$16);
			assert $FieldsNull($h_1$16, $a#1_1$16);
			assert $ReachNull($h_1$16, $a#1_1$16);
			havoc $a#2_1$16; assume !$Allocated($h_1$16,$a#2_1$16);
			$h_1$16:=$Allocate($h_1$16,$a#2_1$16); assume $GoodHeap($h_1$16);
			assume $AllocatedObject($h_1$16, $a#2_1$16);
			assert $FieldsNull($h_1$16, $a#2_1$16);
			assert $ReachNull($h_1$16, $a#2_1$16);
			havoc $a#3_1$16; assume !$Allocated($h_1$16,$a#3_1$16);
			$h_1$16:=$Allocate($h_1$16,$a#3_1$16); assume $GoodHeap($h_1$16);
			assume $AllocatedObject($h_1$16, $a#3_1$16);
			assert $FieldsNull($h_1$16, $a#3_1$16);
			assert $ReachNull($h_1$16, $a#3_1$16);

			// assert (forall $a:Ref :: $ReachableFromParams#1($h_0$0, $a#0_0$0, $a) ==> $a==$Null);

				assume $a#2_0$16 == $a#0_1$16;
				assume $a#3_0$16 == $a#1_1$16;
				assume $a#0_0$16 == $a#2_1$16;
				assume $a#1_0$16 == $a#3_1$16;

			// procedure body _0 start	
		    x_0$16 := x$16 ;
		    assume $ReadObject($h_0$16, x$16);
		    y_0$16 := y$16 ;
		    assume $ReadObject($h_0$16, y$16);
		    if(true )
		    {
		    	$t#0_0$16 := $a#0_0$16 ;
		    	assume $ReadObject($h_0$16, $a#0_0$16);
		    }
		    if(true )
		    {
		    	xn_0$16 := $t#0_0$16 ;
		    	assume $ReadObject($h_0$16, $t#0_0$16);
		    }
		    if(true )
		    {
		    	$h_0$16:=$Write($h_0$16,x_0$16,$field#v,xn_0$16); assume $GoodHeap($h_0$16);
		    }
		    if(true )
		    {
		    	$t#1_0$16 := $a#1_0$16 ;
		    	assume $ReadObject($h_0$16, $a#1_0$16);
		    }
		    if(true )
		    {
		    	yn_0$16 := $t#1_0$16 ;
		    	assume $ReadObject($h_0$16, $t#1_0$16);
		    }
		    if(true )
		    {
		    	$h_0$16:=$Write($h_0$16,y_0$16,$field#v,yn_0$16); assume $GoodHeap($h_0$16);
		    }
		    if(true )
		    {
		    	$t#2_0$16 := $a#2_0$16 ;
		    	assume $ReadObject($h_0$16, $a#2_0$16);
		    }
		    if(true )
		    {
		    	n_0$16 := $t#2_0$16 ;
		    	assume $ReadObject($h_0$16, $t#2_0$16);
		    }
		    if(true )
		    {
		    	$h_0$16:=$Write($h_0$16,yn_0$16,$field#v,n_0$16); assume $GoodHeap($h_0$16);
		    }
		    if(true )
		    {
		    	$h_0$16:=$Write($h_0$16,xn_0$16,$field#v,n_0$16); assume $GoodHeap($h_0$16);
		    }

		    // procedure body _1 start
		    x_1$16 := x$16 ;
		    assume $ReadObject($h_1$16, x$16);
		    y_1$16 := y$16 ;
		    assume $ReadObject($h_1$16, y$16);
		    if(true )
		    {
		    	$t#0_1$16 := $a#0_1$16 ;
		    	assume $ReadObject($h_1$16, $a#0_1$16);
		    }
		    if(true )
		    {
		    	xn_1$16 := $t#0_1$16 ;
		    	assume $ReadObject($h_1$16, $t#0_1$16);
		    }
		    if(true )
		    {
		    	$h_1$16:=$Write($h_1$16,x_1$16,$field#v,xn_1$16); assume $GoodHeap($h_1$16);
		    }
		    if(true )
		    {
		    	$t#1_1$16 := $a#1_1$16 ;
		    	assume $ReadObject($h_1$16, $a#1_1$16);
		    }
		    if(true )
		    {
		    	yn_1$16 := $t#1_1$16 ;
		    	assume $ReadObject($h_1$16, $t#1_1$16);
		    }
		    if(true )
		    {
		    	$h_1$16:=$Write($h_1$16,y_1$16,$field#v,yn_1$16); assume $GoodHeap($h_1$16);
		    }
		    if(true )
		    {
		    	$t#2_1$16 := $a#2_1$16 ;
		    	assume $ReadObject($h_1$16, $a#2_1$16);
		    }
		    if(true )
		    {
		    	xnn_1$16 := $t#2_1$16 ;
		    	assume $ReadObject($h_1$16, $t#2_1$16);
		    }
		    if(true )
		    {
		    	$t#3_1$16 := $a#3_1$16 ;
		    	assume $ReadObject($h_1$16, $a#3_1$16);
		    }
		    if(true )
		    {
		    	ynn_1$16 := $t#3_1$16 ;
		    	assume $ReadObject($h_1$16, $t#3_1$16);
		    }
		    if(true )
		    {
		    	$h_1$16:=$Write($h_1$16,yn_1$16,$field#v,ynn_1$16); assume $GoodHeap($h_1$16);
		    }
		    if(true )
		    {
		    	$h_1$16:=$Write($h_1$16,xn_1$16,$field#v,xnn_1$16); assume $GoodHeap($h_1$16);
		    }

		    // restore heaps
		    $h_0$17 := $h;
		    $h_1$17 := $h;

		    x$17 := x;
		    y$17 := y;

		    // prefix start
			havoc $a#0_0$17; assume !$Allocated($h_0$17,$a#0_0$17);
			$h_0$17:=$Allocate($h_0$17,$a#0_0$17); assume $GoodHeap($h_0$17);
			assume $AllocatedObject($h_0$17, $a#0_0$17);
			assert $FieldsNull($h_0$17, $a#0_0$17);
			assert $ReachNull($h_0$17, $a#0_0$17);
			havoc $a#1_0$17; assume !$Allocated($h_0$17,$a#1_0$17);
			$h_0$17:=$Allocate($h_0$17,$a#1_0$17); assume $GoodHeap($h_0$17);
			assume $AllocatedObject($h_0$17, $a#1_0$17);
			assert $FieldsNull($h_0$17, $a#1_0$17);
			assert $ReachNull($h_0$17, $a#1_0$17);
			havoc $a#2_0$17; assume !$Allocated($h_0$17,$a#2_0$17);
			$h_0$17:=$Allocate($h_0$17,$a#2_0$17); assume $GoodHeap($h_0$17);
			assume $AllocatedObject($h_0$17, $a#2_0$17);
			assert $FieldsNull($h_0$17, $a#2_0$17);
			assert $ReachNull($h_0$17, $a#2_0$17);
			havoc $a#3_0$17; assume !$Allocated($h_0$17,$a#3_0$17);
			$h_0$17:=$Allocate($h_0$17,$a#3_0$17); assume $GoodHeap($h_0$17);
			assume $AllocatedObject($h_0$17, $a#3_0$17);
			assert $FieldsNull($h_0$17, $a#3_0$17);
			assert $ReachNull($h_0$17, $a#3_0$17);
			havoc $a#0_1$17; assume !$Allocated($h_1$17,$a#0_1$17);
			$h_1$17:=$Allocate($h_1$17,$a#0_1$17); assume $GoodHeap($h_1$17);
			assume $AllocatedObject($h_1$17, $a#0_1$17);
			assert $FieldsNull($h_1$17, $a#0_1$17);
			assert $ReachNull($h_1$17, $a#0_1$17);
			havoc $a#1_1$17; assume !$Allocated($h_1$17,$a#1_1$17);
			$h_1$17:=$Allocate($h_1$17,$a#1_1$17); assume $GoodHeap($h_1$17);
			assume $AllocatedObject($h_1$17, $a#1_1$17);
			assert $FieldsNull($h_1$17, $a#1_1$17);
			assert $ReachNull($h_1$17, $a#1_1$17);
			havoc $a#2_1$17; assume !$Allocated($h_1$17,$a#2_1$17);
			$h_1$17:=$Allocate($h_1$17,$a#2_1$17); assume $GoodHeap($h_1$17);
			assume $AllocatedObject($h_1$17, $a#2_1$17);
			assert $FieldsNull($h_1$17, $a#2_1$17);
			assert $ReachNull($h_1$17, $a#2_1$17);
			havoc $a#3_1$17; assume !$Allocated($h_1$17,$a#3_1$17);
			$h_1$17:=$Allocate($h_1$17,$a#3_1$17); assume $GoodHeap($h_1$17);
			assume $AllocatedObject($h_1$17, $a#3_1$17);
			assert $FieldsNull($h_1$17, $a#3_1$17);
			assert $ReachNull($h_1$17, $a#3_1$17);

			// assert (forall $a:Ref :: $ReachableFromParams#1($h_0$0, $a#0_0$0, $a) ==> $a==$Null);

				assume $a#3_0$17 == $a#0_1$17;
				assume $a#2_0$17 == $a#1_1$17;
				assume $a#0_0$17 == $a#2_1$17;
				assume $a#1_0$17 == $a#3_1$17;

			// procedure body _0 start	
		    x_0$17 := x$17 ;
		    assume $ReadObject($h_0$17, x$17);
		    y_0$17 := y$17 ;
		    assume $ReadObject($h_0$17, y$17);
		    if(true )
		    {
		    	$t#0_0$17 := $a#0_0$17 ;
		    	assume $ReadObject($h_0$17, $a#0_0$17);
		    }
		    if(true )
		    {
		    	xn_0$17 := $t#0_0$17 ;
		    	assume $ReadObject($h_0$17, $t#0_0$17);
		    }
		    if(true )
		    {
		    	$h_0$17:=$Write($h_0$17,x_0$17,$field#v,xn_0$17); assume $GoodHeap($h_0$17);
		    }
		    if(true )
		    {
		    	$t#1_0$17 := $a#1_0$17 ;
		    	assume $ReadObject($h_0$17, $a#1_0$17);
		    }
		    if(true )
		    {
		    	yn_0$17 := $t#1_0$17 ;
		    	assume $ReadObject($h_0$17, $t#1_0$17);
		    }
		    if(true )
		    {
		    	$h_0$17:=$Write($h_0$17,y_0$17,$field#v,yn_0$17); assume $GoodHeap($h_0$17);
		    }
		    if(true )
		    {
		    	$t#2_0$17 := $a#2_0$17 ;
		    	assume $ReadObject($h_0$17, $a#2_0$17);
		    }
		    if(true )
		    {
		    	n_0$17 := $t#2_0$17 ;
		    	assume $ReadObject($h_0$17, $t#2_0$17);
		    }
		    if(true )
		    {
		    	$h_0$17:=$Write($h_0$17,yn_0$17,$field#v,n_0$17); assume $GoodHeap($h_0$17);
		    }
		    if(true )
		    {
		    	$h_0$17:=$Write($h_0$17,xn_0$17,$field#v,n_0$17); assume $GoodHeap($h_0$17);
		    }

		    // procedure body _1 start
		    x_1$17 := x$17 ;
		    assume $ReadObject($h_1$17, x$17);
		    y_1$17 := y$17 ;
		    assume $ReadObject($h_1$17, y$17);
		    if(true )
		    {
		    	$t#0_1$17 := $a#0_1$17 ;
		    	assume $ReadObject($h_1$17, $a#0_1$17);
		    }
		    if(true )
		    {
		    	xn_1$17 := $t#0_1$17 ;
		    	assume $ReadObject($h_1$17, $t#0_1$17);
		    }
		    if(true )
		    {
		    	$h_1$17:=$Write($h_1$17,x_1$17,$field#v,xn_1$17); assume $GoodHeap($h_1$17);
		    }
		    if(true )
		    {
		    	$t#1_1$17 := $a#1_1$17 ;
		    	assume $ReadObject($h_1$17, $a#1_1$17);
		    }
		    if(true )
		    {
		    	yn_1$17 := $t#1_1$17 ;
		    	assume $ReadObject($h_1$17, $t#1_1$17);
		    }
		    if(true )
		    {
		    	$h_1$17:=$Write($h_1$17,y_1$17,$field#v,yn_1$17); assume $GoodHeap($h_1$17);
		    }
		    if(true )
		    {
		    	$t#2_1$17 := $a#2_1$17 ;
		    	assume $ReadObject($h_1$17, $a#2_1$17);
		    }
		    if(true )
		    {
		    	xnn_1$17 := $t#2_1$17 ;
		    	assume $ReadObject($h_1$17, $t#2_1$17);
		    }
		    if(true )
		    {
		    	$t#3_1$17 := $a#3_1$17 ;
		    	assume $ReadObject($h_1$17, $a#3_1$17);
		    }
		    if(true )
		    {
		    	ynn_1$17 := $t#3_1$17 ;
		    	assume $ReadObject($h_1$17, $t#3_1$17);
		    }
		    if(true )
		    {
		    	$h_1$17:=$Write($h_1$17,yn_1$17,$field#v,ynn_1$17); assume $GoodHeap($h_1$17);
		    }
		    if(true )
		    {
		    	$h_1$17:=$Write($h_1$17,xn_1$17,$field#v,xnn_1$17); assume $GoodHeap($h_1$17);
		    }

		    // restore heaps
		    $h_0$18 := $h;
		    $h_1$18 := $h;

		    x$18 := x;
		    y$18 := y;

		    // prefix start
			havoc $a#0_0$18; assume !$Allocated($h_0$18,$a#0_0$18);
			$h_0$18:=$Allocate($h_0$18,$a#0_0$18); assume $GoodHeap($h_0$18);
			assume $AllocatedObject($h_0$18, $a#0_0$18);
			assert $FieldsNull($h_0$18, $a#0_0$18);
			assert $ReachNull($h_0$18, $a#0_0$18);
			havoc $a#1_0$18; assume !$Allocated($h_0$18,$a#1_0$18);
			$h_0$18:=$Allocate($h_0$18,$a#1_0$18); assume $GoodHeap($h_0$18);
			assume $AllocatedObject($h_0$18, $a#1_0$18);
			assert $FieldsNull($h_0$18, $a#1_0$18);
			assert $ReachNull($h_0$18, $a#1_0$18);
			havoc $a#2_0$18; assume !$Allocated($h_0$18,$a#2_0$18);
			$h_0$18:=$Allocate($h_0$18,$a#2_0$18); assume $GoodHeap($h_0$18);
			assume $AllocatedObject($h_0$18, $a#2_0$18);
			assert $FieldsNull($h_0$18, $a#2_0$18);
			assert $ReachNull($h_0$18, $a#2_0$18);
			havoc $a#3_0$18; assume !$Allocated($h_0$18,$a#3_0$18);
			$h_0$18:=$Allocate($h_0$18,$a#3_0$18); assume $GoodHeap($h_0$18);
			assume $AllocatedObject($h_0$18, $a#3_0$18);
			assert $FieldsNull($h_0$18, $a#3_0$18);
			assert $ReachNull($h_0$18, $a#3_0$18);
			havoc $a#0_1$18; assume !$Allocated($h_1$18,$a#0_1$18);
			$h_1$18:=$Allocate($h_1$18,$a#0_1$18); assume $GoodHeap($h_1$18);
			assume $AllocatedObject($h_1$18, $a#0_1$18);
			assert $FieldsNull($h_1$18, $a#0_1$18);
			assert $ReachNull($h_1$18, $a#0_1$18);
			havoc $a#1_1$18; assume !$Allocated($h_1$18,$a#1_1$18);
			$h_1$18:=$Allocate($h_1$18,$a#1_1$18); assume $GoodHeap($h_1$18);
			assume $AllocatedObject($h_1$18, $a#1_1$18);
			assert $FieldsNull($h_1$18, $a#1_1$18);
			assert $ReachNull($h_1$18, $a#1_1$18);
			havoc $a#2_1$18; assume !$Allocated($h_1$18,$a#2_1$18);
			$h_1$18:=$Allocate($h_1$18,$a#2_1$18); assume $GoodHeap($h_1$18);
			assume $AllocatedObject($h_1$18, $a#2_1$18);
			assert $FieldsNull($h_1$18, $a#2_1$18);
			assert $ReachNull($h_1$18, $a#2_1$18);
			havoc $a#3_1$18; assume !$Allocated($h_1$18,$a#3_1$18);
			$h_1$18:=$Allocate($h_1$18,$a#3_1$18); assume $GoodHeap($h_1$18);
			assume $AllocatedObject($h_1$18, $a#3_1$18);
			assert $FieldsNull($h_1$18, $a#3_1$18);
			assert $ReachNull($h_1$18, $a#3_1$18);

			// assert (forall $a:Ref :: $ReachableFromParams#1($h_0$0, $a#0_0$0, $a) ==> $a==$Null);

				assume $a#3_0$18 == $a#0_1$18;
				assume $a#2_0$18 == $a#1_1$18;
				assume $a#1_0$18 == $a#2_1$18;
				assume $a#0_0$18 == $a#3_1$18;

			// procedure body _0 start	
		    x_0$18 := x$18 ;
		    assume $ReadObject($h_0$18, x$18);
		    y_0$18 := y$18 ;
		    assume $ReadObject($h_0$18, y$18);
		    if(true )
		    {
		    	$t#0_0$18 := $a#0_0$18 ;
		    	assume $ReadObject($h_0$18, $a#0_0$18);
		    }
		    if(true )
		    {
		    	xn_0$18 := $t#0_0$18 ;
		    	assume $ReadObject($h_0$18, $t#0_0$18);
		    }
		    if(true )
		    {
		    	$h_0$18:=$Write($h_0$18,x_0$18,$field#v,xn_0$18); assume $GoodHeap($h_0$18);
		    }
		    if(true )
		    {
		    	$t#1_0$18 := $a#1_0$18 ;
		    	assume $ReadObject($h_0$18, $a#1_0$18);
		    }
		    if(true )
		    {
		    	yn_0$18 := $t#1_0$18 ;
		    	assume $ReadObject($h_0$18, $t#1_0$18);
		    }
		    if(true )
		    {
		    	$h_0$18:=$Write($h_0$18,y_0$18,$field#v,yn_0$18); assume $GoodHeap($h_0$18);
		    }
		    if(true )
		    {
		    	$t#2_0$18 := $a#2_0$18 ;
		    	assume $ReadObject($h_0$18, $a#2_0$18);
		    }
		    if(true )
		    {
		    	n_0$18 := $t#2_0$18 ;
		    	assume $ReadObject($h_0$18, $t#2_0$18);
		    }
		    if(true )
		    {
		    	$h_0$18:=$Write($h_0$18,yn_0$18,$field#v,n_0$18); assume $GoodHeap($h_0$18);
		    }
		    if(true )
		    {
		    	$h_0$18:=$Write($h_0$18,xn_0$18,$field#v,n_0$18); assume $GoodHeap($h_0$18);
		    }

		    // procedure body _1 start
		    x_1$18 := x$18 ;
		    assume $ReadObject($h_1$18, x$18);
		    y_1$18 := y$18 ;
		    assume $ReadObject($h_1$18, y$18);
		    if(true )
		    {
		    	$t#0_1$18 := $a#0_1$18 ;
		    	assume $ReadObject($h_1$18, $a#0_1$18);
		    }
		    if(true )
		    {
		    	xn_1$18 := $t#0_1$18 ;
		    	assume $ReadObject($h_1$18, $t#0_1$18);
		    }
		    if(true )
		    {
		    	$h_1$18:=$Write($h_1$18,x_1$18,$field#v,xn_1$18); assume $GoodHeap($h_1$18);
		    }
		    if(true )
		    {
		    	$t#1_1$18 := $a#1_1$18 ;
		    	assume $ReadObject($h_1$18, $a#1_1$18);
		    }
		    if(true )
		    {
		    	yn_1$18 := $t#1_1$18 ;
		    	assume $ReadObject($h_1$18, $t#1_1$18);
		    }
		    if(true )
		    {
		    	$h_1$18:=$Write($h_1$18,y_1$18,$field#v,yn_1$18); assume $GoodHeap($h_1$18);
		    }
		    if(true )
		    {
		    	$t#2_1$18 := $a#2_1$18 ;
		    	assume $ReadObject($h_1$18, $a#2_1$18);
		    }
		    if(true )
		    {
		    	xnn_1$18 := $t#2_1$18 ;
		    	assume $ReadObject($h_1$18, $t#2_1$18);
		    }
		    if(true )
		    {
		    	$t#3_1$18 := $a#3_1$18 ;
		    	assume $ReadObject($h_1$18, $a#3_1$18);
		    }
		    if(true )
		    {
		    	ynn_1$18 := $t#3_1$18 ;
		    	assume $ReadObject($h_1$18, $t#3_1$18);
		    }
		    if(true )
		    {
		    	$h_1$18:=$Write($h_1$18,yn_1$18,$field#v,ynn_1$18); assume $GoodHeap($h_1$18);
		    }
		    if(true )
		    {
		    	$h_1$18:=$Write($h_1$18,xn_1$18,$field#v,xnn_1$18); assume $GoodHeap($h_1$18);
		    }

		    // restore heaps
		    $h_0$19 := $h;
		    $h_1$19 := $h;

		    x$19 := x;
		    y$19 := y;

		    // prefix start
			havoc $a#0_0$19; assume !$Allocated($h_0$19,$a#0_0$19);
			$h_0$19:=$Allocate($h_0$19,$a#0_0$19); assume $GoodHeap($h_0$19);
			assume $AllocatedObject($h_0$19, $a#0_0$19);
			assert $FieldsNull($h_0$19, $a#0_0$19);
			assert $ReachNull($h_0$19, $a#0_0$19);
			havoc $a#1_0$19; assume !$Allocated($h_0$19,$a#1_0$19);
			$h_0$19:=$Allocate($h_0$19,$a#1_0$19); assume $GoodHeap($h_0$19);
			assume $AllocatedObject($h_0$19, $a#1_0$19);
			assert $FieldsNull($h_0$19, $a#1_0$19);
			assert $ReachNull($h_0$19, $a#1_0$19);
			havoc $a#2_0$19; assume !$Allocated($h_0$19,$a#2_0$19);
			$h_0$19:=$Allocate($h_0$19,$a#2_0$19); assume $GoodHeap($h_0$19);
			assume $AllocatedObject($h_0$19, $a#2_0$19);
			assert $FieldsNull($h_0$19, $a#2_0$19);
			assert $ReachNull($h_0$19, $a#2_0$19);
			havoc $a#3_0$19; assume !$Allocated($h_0$19,$a#3_0$19);
			$h_0$19:=$Allocate($h_0$19,$a#3_0$19); assume $GoodHeap($h_0$19);
			assume $AllocatedObject($h_0$19, $a#3_0$19);
			assert $FieldsNull($h_0$19, $a#3_0$19);
			assert $ReachNull($h_0$19, $a#3_0$19);
			havoc $a#0_1$19; assume !$Allocated($h_1$19,$a#0_1$19);
			$h_1$19:=$Allocate($h_1$19,$a#0_1$19); assume $GoodHeap($h_1$19);
			assume $AllocatedObject($h_1$19, $a#0_1$19);
			assert $FieldsNull($h_1$19, $a#0_1$19);
			assert $ReachNull($h_1$19, $a#0_1$19);
			havoc $a#1_1$19; assume !$Allocated($h_1$19,$a#1_1$19);
			$h_1$19:=$Allocate($h_1$19,$a#1_1$19); assume $GoodHeap($h_1$19);
			assume $AllocatedObject($h_1$19, $a#1_1$19);
			assert $FieldsNull($h_1$19, $a#1_1$19);
			assert $ReachNull($h_1$19, $a#1_1$19);
			havoc $a#2_1$19; assume !$Allocated($h_1$19,$a#2_1$19);
			$h_1$19:=$Allocate($h_1$19,$a#2_1$19); assume $GoodHeap($h_1$19);
			assume $AllocatedObject($h_1$19, $a#2_1$19);
			assert $FieldsNull($h_1$19, $a#2_1$19);
			assert $ReachNull($h_1$19, $a#2_1$19);
			havoc $a#3_1$19; assume !$Allocated($h_1$19,$a#3_1$19);
			$h_1$19:=$Allocate($h_1$19,$a#3_1$19); assume $GoodHeap($h_1$19);
			assume $AllocatedObject($h_1$19, $a#3_1$19);
			assert $FieldsNull($h_1$19, $a#3_1$19);
			assert $ReachNull($h_1$19, $a#3_1$19);

			// assert (forall $a:Ref :: $ReachableFromParams#1($h_0$0, $a#0_0$0, $a) ==> $a==$Null);

				assume $a#2_0$19 == $a#0_1$19;
				assume $a#3_0$19 == $a#1_1$19;
				assume $a#1_0$19 == $a#2_1$19;
				assume $a#0_0$19 == $a#3_1$19;

			// procedure body _0 start	
		    x_0$19 := x$19 ;
		    assume $ReadObject($h_0$19, x$19);
		    y_0$19 := y$19 ;
		    assume $ReadObject($h_0$19, y$19);
		    if(true )
		    {
		    	$t#0_0$19 := $a#0_0$19 ;
		    	assume $ReadObject($h_0$19, $a#0_0$19);
		    }
		    if(true )
		    {
		    	xn_0$19 := $t#0_0$19 ;
		    	assume $ReadObject($h_0$19, $t#0_0$19);
		    }
		    if(true )
		    {
		    	$h_0$19:=$Write($h_0$19,x_0$19,$field#v,xn_0$19); assume $GoodHeap($h_0$19);
		    }
		    if(true )
		    {
		    	$t#1_0$19 := $a#1_0$19 ;
		    	assume $ReadObject($h_0$19, $a#1_0$19);
		    }
		    if(true )
		    {
		    	yn_0$19 := $t#1_0$19 ;
		    	assume $ReadObject($h_0$19, $t#1_0$19);
		    }
		    if(true )
		    {
		    	$h_0$19:=$Write($h_0$19,y_0$19,$field#v,yn_0$19); assume $GoodHeap($h_0$19);
		    }
		    if(true )
		    {
		    	$t#2_0$19 := $a#2_0$19 ;
		    	assume $ReadObject($h_0$19, $a#2_0$19);
		    }
		    if(true )
		    {
		    	n_0$19 := $t#2_0$19 ;
		    	assume $ReadObject($h_0$19, $t#2_0$19);
		    }
		    if(true )
		    {
		    	$h_0$19:=$Write($h_0$19,yn_0$19,$field#v,n_0$19); assume $GoodHeap($h_0$19);
		    }
		    if(true )
		    {
		    	$h_0$19:=$Write($h_0$19,xn_0$19,$field#v,n_0$19); assume $GoodHeap($h_0$19);
		    }

		    // procedure body _1 start
		    x_1$19 := x$19 ;
		    assume $ReadObject($h_1$19, x$19);
		    y_1$19 := y$19 ;
		    assume $ReadObject($h_1$19, y$19);
		    if(true )
		    {
		    	$t#0_1$19 := $a#0_1$19 ;
		    	assume $ReadObject($h_1$19, $a#0_1$19);
		    }
		    if(true )
		    {
		    	xn_1$19 := $t#0_1$19 ;
		    	assume $ReadObject($h_1$19, $t#0_1$19);
		    }
		    if(true )
		    {
		    	$h_1$19:=$Write($h_1$19,x_1$19,$field#v,xn_1$19); assume $GoodHeap($h_1$19);
		    }
		    if(true )
		    {
		    	$t#1_1$19 := $a#1_1$19 ;
		    	assume $ReadObject($h_1$19, $a#1_1$19);
		    }
		    if(true )
		    {
		    	yn_1$19 := $t#1_1$19 ;
		    	assume $ReadObject($h_1$19, $t#1_1$19);
		    }
		    if(true )
		    {
		    	$h_1$19:=$Write($h_1$19,y_1$19,$field#v,yn_1$19); assume $GoodHeap($h_1$19);
		    }
		    if(true )
		    {
		    	$t#2_1$19 := $a#2_1$19 ;
		    	assume $ReadObject($h_1$19, $a#2_1$19);
		    }
		    if(true )
		    {
		    	xnn_1$19 := $t#2_1$19 ;
		    	assume $ReadObject($h_1$19, $t#2_1$19);
		    }
		    if(true )
		    {
		    	$t#3_1$19 := $a#3_1$19 ;
		    	assume $ReadObject($h_1$19, $a#3_1$19);
		    }
		    if(true )
		    {
		    	ynn_1$19 := $t#3_1$19 ;
		    	assume $ReadObject($h_1$19, $t#3_1$19);
		    }
		    if(true )
		    {
		    	$h_1$19:=$Write($h_1$19,yn_1$19,$field#v,ynn_1$19); assume $GoodHeap($h_1$19);
		    }
		    if(true )
		    {
		    	$h_1$19:=$Write($h_1$19,xn_1$19,$field#v,xnn_1$19); assume $GoodHeap($h_1$19);
		    }

		    // restore heaps
		    $h_0$20 := $h;
		    $h_1$20 := $h;

		    x$20 := x;
		    y$20 := y;

		    // prefix start
			havoc $a#0_0$20; assume !$Allocated($h_0$20,$a#0_0$20);
			$h_0$20:=$Allocate($h_0$20,$a#0_0$20); assume $GoodHeap($h_0$20);
			assume $AllocatedObject($h_0$20, $a#0_0$20);
			assert $FieldsNull($h_0$20, $a#0_0$20);
			assert $ReachNull($h_0$20, $a#0_0$20);
			havoc $a#1_0$20; assume !$Allocated($h_0$20,$a#1_0$20);
			$h_0$20:=$Allocate($h_0$20,$a#1_0$20); assume $GoodHeap($h_0$20);
			assume $AllocatedObject($h_0$20, $a#1_0$20);
			assert $FieldsNull($h_0$20, $a#1_0$20);
			assert $ReachNull($h_0$20, $a#1_0$20);
			havoc $a#2_0$20; assume !$Allocated($h_0$20,$a#2_0$20);
			$h_0$20:=$Allocate($h_0$20,$a#2_0$20); assume $GoodHeap($h_0$20);
			assume $AllocatedObject($h_0$20, $a#2_0$20);
			assert $FieldsNull($h_0$20, $a#2_0$20);
			assert $ReachNull($h_0$20, $a#2_0$20);
			havoc $a#3_0$20; assume !$Allocated($h_0$20,$a#3_0$20);
			$h_0$20:=$Allocate($h_0$20,$a#3_0$20); assume $GoodHeap($h_0$20);
			assume $AllocatedObject($h_0$20, $a#3_0$20);
			assert $FieldsNull($h_0$20, $a#3_0$20);
			assert $ReachNull($h_0$20, $a#3_0$20);
			havoc $a#0_1$20; assume !$Allocated($h_1$20,$a#0_1$20);
			$h_1$20:=$Allocate($h_1$20,$a#0_1$20); assume $GoodHeap($h_1$20);
			assume $AllocatedObject($h_1$20, $a#0_1$20);
			assert $FieldsNull($h_1$20, $a#0_1$20);
			assert $ReachNull($h_1$20, $a#0_1$20);
			havoc $a#1_1$20; assume !$Allocated($h_1$20,$a#1_1$20);
			$h_1$20:=$Allocate($h_1$20,$a#1_1$20); assume $GoodHeap($h_1$20);
			assume $AllocatedObject($h_1$20, $a#1_1$20);
			assert $FieldsNull($h_1$20, $a#1_1$20);
			assert $ReachNull($h_1$20, $a#1_1$20);
			havoc $a#2_1$20; assume !$Allocated($h_1$20,$a#2_1$20);
			$h_1$20:=$Allocate($h_1$20,$a#2_1$20); assume $GoodHeap($h_1$20);
			assume $AllocatedObject($h_1$20, $a#2_1$20);
			assert $FieldsNull($h_1$20, $a#2_1$20);
			assert $ReachNull($h_1$20, $a#2_1$20);
			havoc $a#3_1$20; assume !$Allocated($h_1$20,$a#3_1$20);
			$h_1$20:=$Allocate($h_1$20,$a#3_1$20); assume $GoodHeap($h_1$20);
			assume $AllocatedObject($h_1$20, $a#3_1$20);
			assert $FieldsNull($h_1$20, $a#3_1$20);
			assert $ReachNull($h_1$20, $a#3_1$20);

			// assert (forall $a:Ref :: $ReachableFromParams#1($h_0$0, $a#0_0$0, $a) ==> $a==$Null);

				assume $a#1_0$20 == $a#0_1$20;
				assume $a#3_0$20 == $a#1_1$20;
				assume $a#2_0$20 == $a#2_1$20;
				assume $a#0_0$20 == $a#3_1$20;

			// procedure body _0 start	
		    x_0$20 := x$20 ;
		    assume $ReadObject($h_0$20, x$20);
		    y_0$20 := y$20 ;
		    assume $ReadObject($h_0$20, y$20);
		    if(true )
		    {
		    	$t#0_0$20 := $a#0_0$20 ;
		    	assume $ReadObject($h_0$20, $a#0_0$20);
		    }
		    if(true )
		    {
		    	xn_0$20 := $t#0_0$20 ;
		    	assume $ReadObject($h_0$20, $t#0_0$20);
		    }
		    if(true )
		    {
		    	$h_0$20:=$Write($h_0$20,x_0$20,$field#v,xn_0$20); assume $GoodHeap($h_0$20);
		    }
		    if(true )
		    {
		    	$t#1_0$20 := $a#1_0$20 ;
		    	assume $ReadObject($h_0$20, $a#1_0$20);
		    }
		    if(true )
		    {
		    	yn_0$20 := $t#1_0$20 ;
		    	assume $ReadObject($h_0$20, $t#1_0$20);
		    }
		    if(true )
		    {
		    	$h_0$20:=$Write($h_0$20,y_0$20,$field#v,yn_0$20); assume $GoodHeap($h_0$20);
		    }
		    if(true )
		    {
		    	$t#2_0$20 := $a#2_0$20 ;
		    	assume $ReadObject($h_0$20, $a#2_0$20);
		    }
		    if(true )
		    {
		    	n_0$20 := $t#2_0$20 ;
		    	assume $ReadObject($h_0$20, $t#2_0$20);
		    }
		    if(true )
		    {
		    	$h_0$20:=$Write($h_0$20,yn_0$20,$field#v,n_0$20); assume $GoodHeap($h_0$20);
		    }
		    if(true )
		    {
		    	$h_0$20:=$Write($h_0$20,xn_0$20,$field#v,n_0$20); assume $GoodHeap($h_0$20);
		    }

		    // procedure body _1 start
		    x_1$20 := x$20 ;
		    assume $ReadObject($h_1$20, x$20);
		    y_1$20 := y$20 ;
		    assume $ReadObject($h_1$20, y$20);
		    if(true )
		    {
		    	$t#0_1$20 := $a#0_1$20 ;
		    	assume $ReadObject($h_1$20, $a#0_1$20);
		    }
		    if(true )
		    {
		    	xn_1$20 := $t#0_1$20 ;
		    	assume $ReadObject($h_1$20, $t#0_1$20);
		    }
		    if(true )
		    {
		    	$h_1$20:=$Write($h_1$20,x_1$20,$field#v,xn_1$20); assume $GoodHeap($h_1$20);
		    }
		    if(true )
		    {
		    	$t#1_1$20 := $a#1_1$20 ;
		    	assume $ReadObject($h_1$20, $a#1_1$20);
		    }
		    if(true )
		    {
		    	yn_1$20 := $t#1_1$20 ;
		    	assume $ReadObject($h_1$20, $t#1_1$20);
		    }
		    if(true )
		    {
		    	$h_1$20:=$Write($h_1$20,y_1$20,$field#v,yn_1$20); assume $GoodHeap($h_1$20);
		    }
		    if(true )
		    {
		    	$t#2_1$20 := $a#2_1$20 ;
		    	assume $ReadObject($h_1$20, $a#2_1$20);
		    }
		    if(true )
		    {
		    	xnn_1$20 := $t#2_1$20 ;
		    	assume $ReadObject($h_1$20, $t#2_1$20);
		    }
		    if(true )
		    {
		    	$t#3_1$20 := $a#3_1$20 ;
		    	assume $ReadObject($h_1$20, $a#3_1$20);
		    }
		    if(true )
		    {
		    	ynn_1$20 := $t#3_1$20 ;
		    	assume $ReadObject($h_1$20, $t#3_1$20);
		    }
		    if(true )
		    {
		    	$h_1$20:=$Write($h_1$20,yn_1$20,$field#v,ynn_1$20); assume $GoodHeap($h_1$20);
		    }
		    if(true )
		    {
		    	$h_1$20:=$Write($h_1$20,xn_1$20,$field#v,xnn_1$20); assume $GoodHeap($h_1$20);
		    }

		    // restore heaps
		    $h_0$21 := $h;
		    $h_1$21 := $h;

		    x$21 := x;
		    y$21 := y;

		    // prefix start
			havoc $a#0_0$21; assume !$Allocated($h_0$21,$a#0_0$21);
			$h_0$21:=$Allocate($h_0$21,$a#0_0$21); assume $GoodHeap($h_0$21);
			assume $AllocatedObject($h_0$21, $a#0_0$21);
			assert $FieldsNull($h_0$21, $a#0_0$21);
			assert $ReachNull($h_0$21, $a#0_0$21);
			havoc $a#1_0$21; assume !$Allocated($h_0$21,$a#1_0$21);
			$h_0$21:=$Allocate($h_0$21,$a#1_0$21); assume $GoodHeap($h_0$21);
			assume $AllocatedObject($h_0$21, $a#1_0$21);
			assert $FieldsNull($h_0$21, $a#1_0$21);
			assert $ReachNull($h_0$21, $a#1_0$21);
			havoc $a#2_0$21; assume !$Allocated($h_0$21,$a#2_0$21);
			$h_0$21:=$Allocate($h_0$21,$a#2_0$21); assume $GoodHeap($h_0$21);
			assume $AllocatedObject($h_0$21, $a#2_0$21);
			assert $FieldsNull($h_0$21, $a#2_0$21);
			assert $ReachNull($h_0$21, $a#2_0$21);
			havoc $a#3_0$21; assume !$Allocated($h_0$21,$a#3_0$21);
			$h_0$21:=$Allocate($h_0$21,$a#3_0$21); assume $GoodHeap($h_0$21);
			assume $AllocatedObject($h_0$21, $a#3_0$21);
			assert $FieldsNull($h_0$21, $a#3_0$21);
			assert $ReachNull($h_0$21, $a#3_0$21);
			havoc $a#0_1$21; assume !$Allocated($h_1$21,$a#0_1$21);
			$h_1$21:=$Allocate($h_1$21,$a#0_1$21); assume $GoodHeap($h_1$21);
			assume $AllocatedObject($h_1$21, $a#0_1$21);
			assert $FieldsNull($h_1$21, $a#0_1$21);
			assert $ReachNull($h_1$21, $a#0_1$21);
			havoc $a#1_1$21; assume !$Allocated($h_1$21,$a#1_1$21);
			$h_1$21:=$Allocate($h_1$21,$a#1_1$21); assume $GoodHeap($h_1$21);
			assume $AllocatedObject($h_1$21, $a#1_1$21);
			assert $FieldsNull($h_1$21, $a#1_1$21);
			assert $ReachNull($h_1$21, $a#1_1$21);
			havoc $a#2_1$21; assume !$Allocated($h_1$21,$a#2_1$21);
			$h_1$21:=$Allocate($h_1$21,$a#2_1$21); assume $GoodHeap($h_1$21);
			assume $AllocatedObject($h_1$21, $a#2_1$21);
			assert $FieldsNull($h_1$21, $a#2_1$21);
			assert $ReachNull($h_1$21, $a#2_1$21);
			havoc $a#3_1$21; assume !$Allocated($h_1$21,$a#3_1$21);
			$h_1$21:=$Allocate($h_1$21,$a#3_1$21); assume $GoodHeap($h_1$21);
			assume $AllocatedObject($h_1$21, $a#3_1$21);
			assert $FieldsNull($h_1$21, $a#3_1$21);
			assert $ReachNull($h_1$21, $a#3_1$21);

			// assert (forall $a:Ref :: $ReachableFromParams#1($h_0$0, $a#0_0$0, $a) ==> $a==$Null);

				assume $a#3_0$21 == $a#0_1$21;
				assume $a#1_0$21 == $a#1_1$21;
				assume $a#2_0$21 == $a#2_1$21;
				assume $a#0_0$21 == $a#3_1$21;

			// procedure body _0 start	
		    x_0$21 := x$21 ;
		    assume $ReadObject($h_0$21, x$21);
		    y_0$21 := y$21 ;
		    assume $ReadObject($h_0$21, y$21);
		    if(true )
		    {
		    	$t#0_0$21 := $a#0_0$21 ;
		    	assume $ReadObject($h_0$21, $a#0_0$21);
		    }
		    if(true )
		    {
		    	xn_0$21 := $t#0_0$21 ;
		    	assume $ReadObject($h_0$21, $t#0_0$21);
		    }
		    if(true )
		    {
		    	$h_0$21:=$Write($h_0$21,x_0$21,$field#v,xn_0$21); assume $GoodHeap($h_0$21);
		    }
		    if(true )
		    {
		    	$t#1_0$21 := $a#1_0$21 ;
		    	assume $ReadObject($h_0$21, $a#1_0$21);
		    }
		    if(true )
		    {
		    	yn_0$21 := $t#1_0$21 ;
		    	assume $ReadObject($h_0$21, $t#1_0$21);
		    }
		    if(true )
		    {
		    	$h_0$21:=$Write($h_0$21,y_0$21,$field#v,yn_0$21); assume $GoodHeap($h_0$21);
		    }
		    if(true )
		    {
		    	$t#2_0$21 := $a#2_0$21 ;
		    	assume $ReadObject($h_0$21, $a#2_0$21);
		    }
		    if(true )
		    {
		    	n_0$21 := $t#2_0$21 ;
		    	assume $ReadObject($h_0$21, $t#2_0$21);
		    }
		    if(true )
		    {
		    	$h_0$21:=$Write($h_0$21,yn_0$21,$field#v,n_0$21); assume $GoodHeap($h_0$21);
		    }
		    if(true )
		    {
		    	$h_0$21:=$Write($h_0$21,xn_0$21,$field#v,n_0$21); assume $GoodHeap($h_0$21);
		    }

		    // procedure body _1 start
		    x_1$21 := x$21 ;
		    assume $ReadObject($h_1$21, x$21);
		    y_1$21 := y$21 ;
		    assume $ReadObject($h_1$21, y$21);
		    if(true )
		    {
		    	$t#0_1$21 := $a#0_1$21 ;
		    	assume $ReadObject($h_1$21, $a#0_1$21);
		    }
		    if(true )
		    {
		    	xn_1$21 := $t#0_1$21 ;
		    	assume $ReadObject($h_1$21, $t#0_1$21);
		    }
		    if(true )
		    {
		    	$h_1$21:=$Write($h_1$21,x_1$21,$field#v,xn_1$21); assume $GoodHeap($h_1$21);
		    }
		    if(true )
		    {
		    	$t#1_1$21 := $a#1_1$21 ;
		    	assume $ReadObject($h_1$21, $a#1_1$21);
		    }
		    if(true )
		    {
		    	yn_1$21 := $t#1_1$21 ;
		    	assume $ReadObject($h_1$21, $t#1_1$21);
		    }
		    if(true )
		    {
		    	$h_1$21:=$Write($h_1$21,y_1$21,$field#v,yn_1$21); assume $GoodHeap($h_1$21);
		    }
		    if(true )
		    {
		    	$t#2_1$21 := $a#2_1$21 ;
		    	assume $ReadObject($h_1$21, $a#2_1$21);
		    }
		    if(true )
		    {
		    	xnn_1$21 := $t#2_1$21 ;
		    	assume $ReadObject($h_1$21, $t#2_1$21);
		    }
		    if(true )
		    {
		    	$t#3_1$21 := $a#3_1$21 ;
		    	assume $ReadObject($h_1$21, $a#3_1$21);
		    }
		    if(true )
		    {
		    	ynn_1$21 := $t#3_1$21 ;
		    	assume $ReadObject($h_1$21, $t#3_1$21);
		    }
		    if(true )
		    {
		    	$h_1$21:=$Write($h_1$21,yn_1$21,$field#v,ynn_1$21); assume $GoodHeap($h_1$21);
		    }
		    if(true )
		    {
		    	$h_1$21:=$Write($h_1$21,xn_1$21,$field#v,xnn_1$21); assume $GoodHeap($h_1$21);
		    }

		    // restore heaps
		    $h_0$22 := $h;
		    $h_1$22 := $h;

		    x$22 := x;
		    y$22 := y;

		    // prefix start
			havoc $a#0_0$22; assume !$Allocated($h_0$22,$a#0_0$22);
			$h_0$22:=$Allocate($h_0$22,$a#0_0$22); assume $GoodHeap($h_0$22);
			assume $AllocatedObject($h_0$22, $a#0_0$22);
			assert $FieldsNull($h_0$22, $a#0_0$22);
			assert $ReachNull($h_0$22, $a#0_0$22);
			havoc $a#1_0$22; assume !$Allocated($h_0$22,$a#1_0$22);
			$h_0$22:=$Allocate($h_0$22,$a#1_0$22); assume $GoodHeap($h_0$22);
			assume $AllocatedObject($h_0$22, $a#1_0$22);
			assert $FieldsNull($h_0$22, $a#1_0$22);
			assert $ReachNull($h_0$22, $a#1_0$22);
			havoc $a#2_0$22; assume !$Allocated($h_0$22,$a#2_0$22);
			$h_0$22:=$Allocate($h_0$22,$a#2_0$22); assume $GoodHeap($h_0$22);
			assume $AllocatedObject($h_0$22, $a#2_0$22);
			assert $FieldsNull($h_0$22, $a#2_0$22);
			assert $ReachNull($h_0$22, $a#2_0$22);
			havoc $a#3_0$22; assume !$Allocated($h_0$22,$a#3_0$22);
			$h_0$22:=$Allocate($h_0$22,$a#3_0$22); assume $GoodHeap($h_0$22);
			assume $AllocatedObject($h_0$22, $a#3_0$22);
			assert $FieldsNull($h_0$22, $a#3_0$22);
			assert $ReachNull($h_0$22, $a#3_0$22);
			havoc $a#0_1$22; assume !$Allocated($h_1$22,$a#0_1$22);
			$h_1$22:=$Allocate($h_1$22,$a#0_1$22); assume $GoodHeap($h_1$22);
			assume $AllocatedObject($h_1$22, $a#0_1$22);
			assert $FieldsNull($h_1$22, $a#0_1$22);
			assert $ReachNull($h_1$22, $a#0_1$22);
			havoc $a#1_1$22; assume !$Allocated($h_1$22,$a#1_1$22);
			$h_1$22:=$Allocate($h_1$22,$a#1_1$22); assume $GoodHeap($h_1$22);
			assume $AllocatedObject($h_1$22, $a#1_1$22);
			assert $FieldsNull($h_1$22, $a#1_1$22);
			assert $ReachNull($h_1$22, $a#1_1$22);
			havoc $a#2_1$22; assume !$Allocated($h_1$22,$a#2_1$22);
			$h_1$22:=$Allocate($h_1$22,$a#2_1$22); assume $GoodHeap($h_1$22);
			assume $AllocatedObject($h_1$22, $a#2_1$22);
			assert $FieldsNull($h_1$22, $a#2_1$22);
			assert $ReachNull($h_1$22, $a#2_1$22);
			havoc $a#3_1$22; assume !$Allocated($h_1$22,$a#3_1$22);
			$h_1$22:=$Allocate($h_1$22,$a#3_1$22); assume $GoodHeap($h_1$22);
			assume $AllocatedObject($h_1$22, $a#3_1$22);
			assert $FieldsNull($h_1$22, $a#3_1$22);
			assert $ReachNull($h_1$22, $a#3_1$22);

			// assert (forall $a:Ref :: $ReachableFromParams#1($h_0$0, $a#0_0$0, $a) ==> $a==$Null);

				assume $a#2_0$22 == $a#0_1$22;
				assume $a#1_0$22 == $a#1_1$22;
				assume $a#3_0$22 == $a#2_1$22;
				assume $a#0_0$22 == $a#3_1$22;

			// procedure body _0 start	
		    x_0$22 := x$22 ;
		    assume $ReadObject($h_0$22, x$22);
		    y_0$22 := y$22 ;
		    assume $ReadObject($h_0$22, y$22);
		    if(true )
		    {
		    	$t#0_0$22 := $a#0_0$22 ;
		    	assume $ReadObject($h_0$22, $a#0_0$22);
		    }
		    if(true )
		    {
		    	xn_0$22 := $t#0_0$22 ;
		    	assume $ReadObject($h_0$22, $t#0_0$22);
		    }
		    if(true )
		    {
		    	$h_0$22:=$Write($h_0$22,x_0$22,$field#v,xn_0$22); assume $GoodHeap($h_0$22);
		    }
		    if(true )
		    {
		    	$t#1_0$22 := $a#1_0$22 ;
		    	assume $ReadObject($h_0$22, $a#1_0$22);
		    }
		    if(true )
		    {
		    	yn_0$22 := $t#1_0$22 ;
		    	assume $ReadObject($h_0$22, $t#1_0$22);
		    }
		    if(true )
		    {
		    	$h_0$22:=$Write($h_0$22,y_0$22,$field#v,yn_0$22); assume $GoodHeap($h_0$22);
		    }
		    if(true )
		    {
		    	$t#2_0$22 := $a#2_0$22 ;
		    	assume $ReadObject($h_0$22, $a#2_0$22);
		    }
		    if(true )
		    {
		    	n_0$22 := $t#2_0$22 ;
		    	assume $ReadObject($h_0$22, $t#2_0$22);
		    }
		    if(true )
		    {
		    	$h_0$22:=$Write($h_0$22,yn_0$22,$field#v,n_0$22); assume $GoodHeap($h_0$22);
		    }
		    if(true )
		    {
		    	$h_0$22:=$Write($h_0$22,xn_0$22,$field#v,n_0$22); assume $GoodHeap($h_0$22);
		    }

		    // procedure body _1 start
		    x_1$22 := x$22 ;
		    assume $ReadObject($h_1$22, x$22);
		    y_1$22 := y$22 ;
		    assume $ReadObject($h_1$22, y$22);
		    if(true )
		    {
		    	$t#0_1$22 := $a#0_1$22 ;
		    	assume $ReadObject($h_1$22, $a#0_1$22);
		    }
		    if(true )
		    {
		    	xn_1$22 := $t#0_1$22 ;
		    	assume $ReadObject($h_1$22, $t#0_1$22);
		    }
		    if(true )
		    {
		    	$h_1$22:=$Write($h_1$22,x_1$22,$field#v,xn_1$22); assume $GoodHeap($h_1$22);
		    }
		    if(true )
		    {
		    	$t#1_1$22 := $a#1_1$22 ;
		    	assume $ReadObject($h_1$22, $a#1_1$22);
		    }
		    if(true )
		    {
		    	yn_1$22 := $t#1_1$22 ;
		    	assume $ReadObject($h_1$22, $t#1_1$22);
		    }
		    if(true )
		    {
		    	$h_1$22:=$Write($h_1$22,y_1$22,$field#v,yn_1$22); assume $GoodHeap($h_1$22);
		    }
		    if(true )
		    {
		    	$t#2_1$22 := $a#2_1$22 ;
		    	assume $ReadObject($h_1$22, $a#2_1$22);
		    }
		    if(true )
		    {
		    	xnn_1$22 := $t#2_1$22 ;
		    	assume $ReadObject($h_1$22, $t#2_1$22);
		    }
		    if(true )
		    {
		    	$t#3_1$22 := $a#3_1$22 ;
		    	assume $ReadObject($h_1$22, $a#3_1$22);
		    }
		    if(true )
		    {
		    	ynn_1$22 := $t#3_1$22 ;
		    	assume $ReadObject($h_1$22, $t#3_1$22);
		    }
		    if(true )
		    {
		    	$h_1$22:=$Write($h_1$22,yn_1$22,$field#v,ynn_1$22); assume $GoodHeap($h_1$22);
		    }
		    if(true )
		    {
		    	$h_1$22:=$Write($h_1$22,xn_1$22,$field#v,xnn_1$22); assume $GoodHeap($h_1$22);
		    }

		    // restore heaps
		    $h_0$23 := $h;
		    $h_1$23 := $h;

		    x$23 := x;
		    y$23 := y;

		    // prefix start
			havoc $a#0_0$23; assume !$Allocated($h_0$23,$a#0_0$23);
			$h_0$23:=$Allocate($h_0$23,$a#0_0$23); assume $GoodHeap($h_0$23);
			assume $AllocatedObject($h_0$23, $a#0_0$23);
			assert $FieldsNull($h_0$23, $a#0_0$23);
			assert $ReachNull($h_0$23, $a#0_0$23);
			havoc $a#1_0$23; assume !$Allocated($h_0$23,$a#1_0$23);
			$h_0$23:=$Allocate($h_0$23,$a#1_0$23); assume $GoodHeap($h_0$23);
			assume $AllocatedObject($h_0$23, $a#1_0$23);
			assert $FieldsNull($h_0$23, $a#1_0$23);
			assert $ReachNull($h_0$23, $a#1_0$23);
			havoc $a#2_0$23; assume !$Allocated($h_0$23,$a#2_0$23);
			$h_0$23:=$Allocate($h_0$23,$a#2_0$23); assume $GoodHeap($h_0$23);
			assume $AllocatedObject($h_0$23, $a#2_0$23);
			assert $FieldsNull($h_0$23, $a#2_0$23);
			assert $ReachNull($h_0$23, $a#2_0$23);
			havoc $a#3_0$23; assume !$Allocated($h_0$23,$a#3_0$23);
			$h_0$23:=$Allocate($h_0$23,$a#3_0$23); assume $GoodHeap($h_0$23);
			assume $AllocatedObject($h_0$23, $a#3_0$23);
			assert $FieldsNull($h_0$23, $a#3_0$23);
			assert $ReachNull($h_0$23, $a#3_0$23);
			havoc $a#0_1$23; assume !$Allocated($h_1$23,$a#0_1$23);
			$h_1$23:=$Allocate($h_1$23,$a#0_1$23); assume $GoodHeap($h_1$23);
			assume $AllocatedObject($h_1$23, $a#0_1$23);
			assert $FieldsNull($h_1$23, $a#0_1$23);
			assert $ReachNull($h_1$23, $a#0_1$23);
			havoc $a#1_1$23; assume !$Allocated($h_1$23,$a#1_1$23);
			$h_1$23:=$Allocate($h_1$23,$a#1_1$23); assume $GoodHeap($h_1$23);
			assume $AllocatedObject($h_1$23, $a#1_1$23);
			assert $FieldsNull($h_1$23, $a#1_1$23);
			assert $ReachNull($h_1$23, $a#1_1$23);
			havoc $a#2_1$23; assume !$Allocated($h_1$23,$a#2_1$23);
			$h_1$23:=$Allocate($h_1$23,$a#2_1$23); assume $GoodHeap($h_1$23);
			assume $AllocatedObject($h_1$23, $a#2_1$23);
			assert $FieldsNull($h_1$23, $a#2_1$23);
			assert $ReachNull($h_1$23, $a#2_1$23);
			havoc $a#3_1$23; assume !$Allocated($h_1$23,$a#3_1$23);
			$h_1$23:=$Allocate($h_1$23,$a#3_1$23); assume $GoodHeap($h_1$23);
			assume $AllocatedObject($h_1$23, $a#3_1$23);
			assert $FieldsNull($h_1$23, $a#3_1$23);
			assert $ReachNull($h_1$23, $a#3_1$23);

			// assert (forall $a:Ref :: $ReachableFromParams#1($h_0$0, $a#0_0$0, $a) ==> $a==$Null);

				assume $a#1_0$23 == $a#0_1$23;
				assume $a#2_0$23 == $a#1_1$23;
				assume $a#3_0$23 == $a#2_1$23;
				assume $a#0_0$23 == $a#3_1$23;

			// procedure body _0 start	
		    x_0$23 := x$23 ;
		    assume $ReadObject($h_0$23, x$23);
		    y_0$23 := y$23 ;
		    assume $ReadObject($h_0$23, y$23);
		    if(true )
		    {
		    	$t#0_0$23 := $a#0_0$23 ;
		    	assume $ReadObject($h_0$23, $a#0_0$23);
		    }
		    if(true )
		    {
		    	xn_0$23 := $t#0_0$23 ;
		    	assume $ReadObject($h_0$23, $t#0_0$23);
		    }
		    if(true )
		    {
		    	$h_0$23:=$Write($h_0$23,x_0$23,$field#v,xn_0$23); assume $GoodHeap($h_0$23);
		    }
		    if(true )
		    {
		    	$t#1_0$23 := $a#1_0$23 ;
		    	assume $ReadObject($h_0$23, $a#1_0$23);
		    }
		    if(true )
		    {
		    	yn_0$23 := $t#1_0$23 ;
		    	assume $ReadObject($h_0$23, $t#1_0$23);
		    }
		    if(true )
		    {
		    	$h_0$23:=$Write($h_0$23,y_0$23,$field#v,yn_0$23); assume $GoodHeap($h_0$23);
		    }
		    if(true )
		    {
		    	$t#2_0$23 := $a#2_0$23 ;
		    	assume $ReadObject($h_0$23, $a#2_0$23);
		    }
		    if(true )
		    {
		    	n_0$23 := $t#2_0$23 ;
		    	assume $ReadObject($h_0$23, $t#2_0$23);
		    }
		    if(true )
		    {
		    	$h_0$23:=$Write($h_0$23,yn_0$23,$field#v,n_0$23); assume $GoodHeap($h_0$23);
		    }
		    if(true )
		    {
		    	$h_0$23:=$Write($h_0$23,xn_0$23,$field#v,n_0$23); assume $GoodHeap($h_0$23);
		    }

		    // procedure body _1 start
		    x_1$23 := x$23 ;
		    assume $ReadObject($h_1$23, x$23);
		    y_1$23 := y$23 ;
		    assume $ReadObject($h_1$23, y$23);
		    if(true )
		    {
		    	$t#0_1$23 := $a#0_1$23 ;
		    	assume $ReadObject($h_1$23, $a#0_1$23);
		    }
		    if(true )
		    {
		    	xn_1$23 := $t#0_1$23 ;
		    	assume $ReadObject($h_1$23, $t#0_1$23);
		    }
		    if(true )
		    {
		    	$h_1$23:=$Write($h_1$23,x_1$23,$field#v,xn_1$23); assume $GoodHeap($h_1$23);
		    }
		    if(true )
		    {
		    	$t#1_1$23 := $a#1_1$23 ;
		    	assume $ReadObject($h_1$23, $a#1_1$23);
		    }
		    if(true )
		    {
		    	yn_1$23 := $t#1_1$23 ;
		    	assume $ReadObject($h_1$23, $t#1_1$23);
		    }
		    if(true )
		    {
		    	$h_1$23:=$Write($h_1$23,y_1$23,$field#v,yn_1$23); assume $GoodHeap($h_1$23);
		    }
		    if(true )
		    {
		    	$t#2_1$23 := $a#2_1$23 ;
		    	assume $ReadObject($h_1$23, $a#2_1$23);
		    }
		    if(true )
		    {
		    	xnn_1$23 := $t#2_1$23 ;
		    	assume $ReadObject($h_1$23, $t#2_1$23);
		    }
		    if(true )
		    {
		    	$t#3_1$23 := $a#3_1$23 ;
		    	assume $ReadObject($h_1$23, $a#3_1$23);
		    }
		    if(true )
		    {
		    	ynn_1$23 := $t#3_1$23 ;
		    	assume $ReadObject($h_1$23, $t#3_1$23);
		    }
		    if(true )
		    {
		    	$h_1$23:=$Write($h_1$23,yn_1$23,$field#v,ynn_1$23); assume $GoodHeap($h_1$23);
		    }
		    if(true )
		    {
		    	$h_1$23:=$Write($h_1$23,xn_1$23,$field#v,xnn_1$23); assume $GoodHeap($h_1$23);
		    }


	assert 
		$Isomorphism($h_0$0, $h_1$0, $roots) ||
		$Isomorphism($h_0$1, $h_1$1, $roots) ||
		$Isomorphism($h_0$2, $h_1$2, $roots) ||
		$Isomorphism($h_0$3, $h_1$3, $roots) ||
		$Isomorphism($h_0$4, $h_1$4, $roots) ||
		$Isomorphism($h_0$5, $h_1$5, $roots) ||
		$Isomorphism($h_0$6, $h_1$6, $roots) ||
		$Isomorphism($h_0$7, $h_1$7, $roots) ||
		$Isomorphism($h_0$8, $h_1$8, $roots) ||
		$Isomorphism($h_0$9, $h_1$9, $roots) ||
		$Isomorphism($h_0$10, $h_1$10, $roots) ||
		$Isomorphism($h_0$11, $h_1$11, $roots) ||
		$Isomorphism($h_0$12, $h_1$12, $roots) ||
		$Isomorphism($h_0$13, $h_1$13, $roots) ||
		$Isomorphism($h_0$14, $h_1$14, $roots) ||
		$Isomorphism($h_0$15, $h_1$15, $roots) ||
		$Isomorphism($h_0$16, $h_1$16, $roots) ||
		$Isomorphism($h_0$17, $h_1$17, $roots) ||
		$Isomorphism($h_0$18, $h_1$18, $roots) ||
		$Isomorphism($h_0$19, $h_1$19, $roots) ||
		$Isomorphism($h_0$20, $h_1$20, $roots) ||
		$Isomorphism($h_0$21, $h_1$21, $roots) ||
		$Isomorphism($h_0$22, $h_1$22, $roots) ||
		$Isomorphism($h_0$23, $h_1$23, $roots);	
}