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
axiom (forall <alpha> $f:Field alpha :: $f==$E || $f==$F || $f==$G || $f==$Alloc);

type Heap = <alpha>[Ref, Field alpha] alpha;

/////////////////////////////////////////////////////////////////////////////
// Well Formed Heap
function $GoodHeap($h:Heap) : bool;
axiom (forall $h:Heap :: $GoodHeap($h) ==> (forall $a:Ref,$f:Field Ref :: !$Allocated($h, $a) ==> $Edge($h,$a,$f, $Null)));
axiom (forall $h:Heap :: $GoodHeap($h) ==> (forall $a:Ref,$f:Field Ref :: $Allocated($h, $a) ==> $Allocated($h, $Read($h,$a,$f))));
axiom (forall $h:Heap :: $GoodHeap($h) ==> $Allocated($h, $Null));
axiom (forall $h:Heap :: $GoodHeap($h) ==> (forall $f:Field Ref :: $Edge($h,$Null,$f, $Null)));
axiom (forall $h:Heap :: $GoodHeap($h) ==> (exists $a:Ref :: !$Allocated($h, $a))); // always a free address - is this needed?

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

function $Allocator($h:Heap) : Ref;
axiom (forall $h:Heap, $a:Ref :: $Allocator($h)==$a ==> !$Allocated($h,$a));


/////////////////////////////////////////////////////////////////////////////
// Roots
type Roots;
function $Root(roots:Roots, a:Ref) : bool;

function $Roots#Allocated($roots:Roots, $h:Heap) : bool
{
    (forall $a:Ref :: $Root($roots, $a) ==> $Allocated($h, $a))
}

function $SameDiff($hpre_1, $hpost_1, $hpre_2, $hpost_2:Heap) : bool;


axiom (forall $hpre_1, $hpost_1, $hpre_2, $hpost_2:Heap ::
		$SameDiff($hpre_1, $hpost_1, $hpre_2, $hpost_2) 
		==>
		   // (forall $a:Ref :: $Allocated($hpre_1, $a) != $Allocated($hpost_1, $a) <==> $Allocated($hpre_2, $a) != $Allocated($hpost_2, $a))
		      (forall <alpha> $a:Ref,$f:Field alpha :: $Read($hpre_1, $a, $f) == $Read($hpost_1, $a, $f) <==> $Read($hpre_2, $a, $f) == $Read($hpost_2, $a, $f))
		   && (forall <alpha> $a:Ref,$f:Field alpha :: $Read($hpre_1, $a, $f) != $Read($hpost_1, $a, $f) ==> $Read($hpost_1, $a, $f)==$Read($hpost_2, $a, $f))
	);


/////////////////////////////////////////////////////////////////////////////
// Extensional Equality
function $Heap#Equal($h_1, $h_2:Heap) : bool
{
   (forall <alpha> $f:Field alpha, $a:Ref :: $Read($h_1, $a, $f) == $Read($h_2, $a, $f))
}

/////////////////////////////////////////////////////////////////////////////
// Isomorphism
function $Isomorphism($h_1, $h_2:Heap, $roots:Roots) : bool;

// equal heaps are isomorphic
axiom (forall $heap:Heap, $roots:Roots :: 
			(forall $a:Ref :: $Root($roots, $a) ==> $Allocated($heap, $a))
		==> 
			$Isomorphism($heap, $heap, $roots));

// extensionally equal heaps are isomorphic
axiom (forall $h_1,$h_2:Heap, $roots:Roots :: 
			   (forall $a:Ref :: $Root($roots, $a) ==> $Allocated($h_1, $a))
			&& $Heap#Equal($h_1, $h_2)   
		==> 
			$Isomorphism($h_1, $h_2, $roots));
			
// same diff on isomorphic heaps preserves isomorphism
axiom (forall $hpre_1, $hpost_1, $hpre_2, $hpost_2:Heap, $roots:Roots :: 
			$Isomorphism($hpre_1, $hpre_2, $roots) &&
			$SameDiff($hpre_1, $hpost_1, $hpre_2, $hpost_2) 
			==>
			$Isomorphism($hpost_1, $hpost_2, $roots)
	   );
 

///////////////////////////////////////////////////////
var $h_1:Heap where $GoodHeap($h_1);
var $h_2:Heap where $GoodHeap($h_2);

///////////////////////////////////////////////////////

procedure $SwapPreservesIdentityIso($roots:Roots, x:Ref)
	modifies $h_1,$h_2;
	requires $Heap#Equal($h_1, $h_2);
	requires $Isomorphism($h_1, $h_2, $roots);	
	requires $Allocated($h_1, x);
    requires $Roots#Allocated($roots, $h_1);
	requires $GoodHeap($h_1);
	requires (forall a:Ref :: $Allocated($h_1, a) == $Root($roots, a));
{ 
   var tE_1,tF_1,tE_2,tF_2 : Ref;
   
   tE_1 := $Read($h_1, x, $E); assert($Allocated($h_1, tE_1));
   tF_1 := $Read($h_1, x, $F); assert($Allocated($h_1, tF_1));
   $h_1 := $Write($h_1, x, $E, tF_1); assume $GoodHeap($h_1);
   $h_1 := $Write($h_1, x, $F, tE_1); assume $GoodHeap($h_1);

   tE_2 := $Read($h_2, x, $E); assert($Allocated($h_2, tE_2));
   tF_2 := $Read($h_2, x, $F); assert($Allocated($h_2, tF_2));
   $h_2 := $Write($h_2, x, $E, tF_2); assume $GoodHeap($h_2);
   $h_2 := $Write($h_2, x, $F, tE_2); assume $GoodHeap($h_2);
   
   assert $Isomorphism($h_1, $h_2, $roots);
}

procedure $CallPreservesIso($roots:Roots, x:Ref)
	modifies $h_1,$h_2;
	requires $Heap#Equal($h_1, $h_2);
	requires $Isomorphism($h_1, $h_2, $roots);	
	requires $Allocated($h_1, x);
    requires $Roots#Allocated($roots, $h_1);
	requires $GoodHeap($h_1);
	requires (forall a:Ref :: $Allocated($h_1, a) == $Root($roots, a));
{ 
   var tE_1,tF_1,tE_2,tF_2 : Ref;
   var $c1_1:bool,$c1_hpre_1,$c1_hpost_1:Heap,$c1_x_1:Ref;
   var $c1_2:bool,$c1_hpre_2,$c1_hpost_2:Heap,$c1_x_2:Ref;
   
   tE_1 := $Read($h_1, x, $E); assert($Allocated($h_1, tE_1));
   $c1_1 := true; $c1_hpre_1 := $h_1; $c1_x_1 := tE_1;
   call $ProcedureF_1(tE_1);
   $c1_hpost_1 := $h_1;

   tE_2 := $Read($h_2, x, $E); assert($Allocated($h_2, tE_2));
   $c1_2 := true; $c1_hpre_2 := $h_2; $c1_x_2 := tE_2;
   call $ProcedureF_2(tE_2);
   $c1_hpost_2 := $h_2;
   
   assume $c1_1 && $c1_2 && $Isomorphism($c1_hpre_1, $c1_hpre_2, $roots) ==> $SameDiff($c1_hpre_1, $c1_hpost_1, $c1_hpre_2, $c1_hpost_2); 
     
   assert $Isomorphism($h_1, $h_2, $roots);
}

procedure $CallThenNoopPreservesIso($roots:Roots, x:Ref)
	modifies $h_1,$h_2;
	requires $Heap#Equal($h_1, $h_2);
	requires $Isomorphism($h_1, $h_2, $roots);	
	requires $Allocated($h_1, x);
    requires $Roots#Allocated($roots, $h_1);
	requires $GoodHeap($h_1);
	requires (forall a:Ref :: $Allocated($h_1, a) == $Root($roots, a));
{ 
   var tE_1,tF_1,tE_2,tF_2 : Ref;
   var $c1_1:bool,$c1_hpre_1,$c1_hpost_1:Heap,$c1_x_1:Ref;
   var $c1_2:bool,$c1_hpre_2,$c1_hpost_2:Heap,$c1_x_2:Ref;
   
   tE_1 := $Read($h_1, x, $E); assert($Allocated($h_1, tE_1));
   $c1_1 := true; $c1_hpre_1 := $h_1; $c1_x_1 := tE_1;
   call $ProcedureF_1(tE_1);
   $c1_hpost_1 := $h_1;
   
   tE_1 := $Read($h_1, x, $E); assert($Allocated($h_1, tE_1));
   $h_1 := $Write($h_1, x, $E, tE_1); assume $GoodHeap($h_1);

   tE_2 := $Read($h_2, x, $E); assert($Allocated($h_2, tE_2));
   $c1_2 := true; $c1_hpre_2 := $h_2; $c1_x_2 := tE_2;
   call $ProcedureF_2(tE_2);
   $c1_hpost_2 := $h_2;
   
   assume $c1_1 && $c1_2 && $Isomorphism($c1_hpre_1, $c1_hpre_2, $roots) ==> $SameDiff($c1_hpre_1, $c1_hpost_1, $c1_hpre_2, $c1_hpost_2);    
   assert $Isomorphism($h_1, $h_2, $roots);
}

procedure $CallThenWritePreservesIso($roots:Roots, x:Ref)
	modifies $h_1,$h_2;
	requires $Heap#Equal($h_1, $h_2);
	requires $Isomorphism($h_1, $h_2, $roots);	
	requires $Allocated($h_1, x);
    requires $Roots#Allocated($roots, $h_1);
	requires $GoodHeap($h_1);
	requires (forall a:Ref :: $Allocated($h_1, a) == $Root($roots, a));
{ 
   var tE_1,tF_1,tE_2,tF_2 : Ref;
   var $c1_1:bool,$c1_hpre_1,$c1_hpost_1:Heap,$c1_x_1:Ref;
   var $c1_2:bool,$c1_hpre_2,$c1_hpost_2:Heap,$c1_x_2:Ref;
   
   tE_1 := $Read($h_1, x, $E); assert($Allocated($h_1, tE_1));
   $c1_1 := true; $c1_hpre_1 := $h_1; $c1_x_1 := tE_1;
   call $ProcedureF_1(tE_1);
   $c1_hpost_1 := $h_1;
   
   tE_1 := $Read($h_1, x, $E); assert($Allocated($h_1, tE_1));
   $h_1 := $Write($h_1, x, $F, tE_1); assume $GoodHeap($h_1);

   tE_2 := $Read($h_2, x, $E); assert($Allocated($h_2, tE_2));
   $c1_2 := true; $c1_hpre_2 := $h_2; $c1_x_2 := tE_2;
   call $ProcedureF_2(tE_2);
   $c1_hpost_2 := $h_2;
   
   tE_2 := $Read($h_2, x, $E); assert($Allocated($h_2, tE_2));
   $h_2 := $Write($h_2, x, $F, tE_2); assume $GoodHeap($h_2);
   
   assume $c1_1 && $c1_2 && $Isomorphism($c1_hpre_1, $c1_hpre_2, $roots) ==> $SameDiff($c1_hpre_1, $c1_hpost_1, $c1_hpre_2, $c1_hpost_2);    
   assert $Isomorphism($h_1, $h_2, $roots);
}

type SK;
function $SK(sk:SK,$a:Ref):Ref;

procedure $CanAssertEqualityOfAllocation($roots:Roots, x:Ref)
	modifies $h_1,$h_2;
	requires $Heap#Equal($h_1, $h_2);
	requires $Isomorphism($h_1, $h_2, $roots);	
	requires $Allocated($h_1, x);
    requires $Roots#Allocated($roots, $h_1);
	requires $GoodHeap($h_1);
	requires (forall a:Ref :: $Allocated($h_1, a) == $Root($roots, a));
{
	var t_1, t_2:Ref;
	
	havoc t_1; assume $Allocator($h_1) == t_1;
	$h_1 := $Allocate($h_1,t_1); assert($Allocated($h_1, t_1)); assume $GoodHeap($h_1);
	$h_1 := $Write($h_1, x, $F, t_1); assume $GoodHeap($h_1);
	
	havoc t_2; assume $Allocator($h_2) == t_2;
	$h_2 := $Allocate($h_2,t_2); assert($Allocated($h_2, t_2)); assume $GoodHeap($h_2);
	$h_2 := $Write($h_2, x, $F, t_2); assume $GoodHeap($h_2);
	
	// Is there an interpretation of function "$Allocator" that would makes $h_1 == $h_2?
	// Yes, all interpretations that make t_1 == t_2...  
	assume t_1 == t_2;
	
	assert $Heap#Equal($h_1, $h_2);
	assert $Isomorphism($h_1, $h_2, $roots);
}

procedure $AllocationStrategyAsDisjunction($roots:Roots, x:Ref)
	modifies $h_1,$h_2;
	requires $Heap#Equal($h_1, $h_2);
	requires $Isomorphism($h_1, $h_2, $roots);	
	requires $Allocated($h_1, x);
    requires $Roots#Allocated($roots, $h_1);
	requires $GoodHeap($h_1);
	requires (forall a:Ref :: $Allocated($h_1, a) == $Root($roots, a));
{
	var ta_1, ta_2:Ref;
	var tb_1, tb_2:Ref;
	
	c1_1 := false;
	c2_1 := false;
	
	// P1
	havoc ta_1; assume !$Allocated($h_1, ta_1);
	$h_1 := $Allocate($h_1,ta_1); assert($Allocated($h_1, ta_1)); assume $GoodHeap($h_1);
	havoc tb_1; assume !$Allocated($h_1, tb_1);
	$h_1 := $Allocate($h_1,tb_1); assert($Allocated($h_1, tb_1)); assume $GoodHeap($h_1);
	if (x.H == null) {
	c1_1 := true;
	$h_1 := $Write($h_1, x, $F, ta_1); assume $GoodHeap($h_1);
	$h_1 := $Write($h_1, x, $G, tb_1); assume $GoodHeap($h_1);
	} else {
	c2_1 := true;
	$h_1 := $Write($h_1, x, $G, ta_1); assume $GoodHeap($h_1);
	$h_1 := $Write($h_1, x, $F, tb_1); assume $GoodHeap($h_1);
	}
	
	c1_2 := false;
	c2_2 := false;
	// P2
	havoc ta_2; assume !$Allocated($h_2, ta_2);
	$h_2 := $Allocate($h_2,ta_2); assert($Allocated($h_2, ta_2)); assume $GoodHeap($h_2);
	havoc tb_2; assume !$Allocated($h_2, tb_2);
	$h_2 := $Allocate($h_2,tb_2); assert($Allocated($h_2, tb_2)); assume $GoodHeap($h_2);
	if (x.H == null) {
	c1_2 := true;
	$h_2 := $Write($h_2, x, $G, ta_2); assume $GoodHeap($h_2);
	$h_2 := $Write($h_2, x, $F, tb_2); assume $GoodHeap($h_2);
	} else {
	c2_2 := true;
	$h_2 := $Write($h_2, x, $F, ta_2); assume $GoodHeap($h_2);
	$h_2 := $Write($h_2, x, $G, tb_2); assume $GoodHeap($h_2);
	}
	
	// Is there an allocation strategy that makes $h_1 == $h_2?
	// Yes, any strategy that makes ta_1 == ta_2 && tb_1 == tb_2...  
	assert c1_1 && c1_2 ==>
	       (ta_1 == ta_2 && tb_1 == tb_2 ==> $Heap#Equal($h_1, $h_2)) || 
	       (ta_1 == tb_2 && tb_1 == ta_2 ==> $Heap#Equal($h_1, $h_2));
	assert c1_1 && c2_2 ==>
	       (ta_1 == ta_2 && tb_1 == tb_2 ==> $Heap#Equal($h_1, $h_2)) || 
	       (ta_1 == tb_2 && tb_1 == ta_2 ==> $Heap#Equal($h_1, $h_2));
	...
}

function Uf(x:int):Ref;
axiom (forall a:Ref :: (exists x:int :: Uf(x) == a)); 

procedure $AllocationStrategyAsUf($roots:Roots, x:Ref)
	modifies $h_1,$h_2;
	requires $Heap#Equal($h_1, $h_2);
	requires $Isomorphism($h_1, $h_2, $roots);	
	requires $Allocated($h_1, x);
    requires $Roots#Allocated($roots, $h_1);
	requires $GoodHeap($h_1);
	requires (forall a:Ref :: $Allocated($h_1, a) == $Root($roots, a));
{
	var ta_1, ta_2:Ref;
	var tb_1, tb_2:Ref;
	
	havoc ta_1; assume !$Allocated($h_1, ta_1);
	$h_1 := $Allocate($h_1,ta_1); assert($Allocated($h_1, ta_1)); assume $GoodHeap($h_1);
	havoc tb_1; assume !$Allocated($h_1, tb_1);
	$h_1 := $Allocate($h_1,tb_1); assert($Allocated($h_1, tb_1)); assume $GoodHeap($h_1);
	$h_1 := $Write($h_1, x, $F, ta_1); assume $GoodHeap($h_1);
	$h_1 := $Write($h_1, x, $G, tb_1); assume $GoodHeap($h_1);
	
	havoc ta_2; assume !$Allocated($h_2, ta_2);
	$h_2 := $Allocate($h_2,ta_2); assert($Allocated($h_2, ta_2)); assume $GoodHeap($h_2);
	havoc tb_2; assume !$Allocated($h_2, tb_2);
	$h_2 := $Allocate($h_2,tb_2); assert($Allocated($h_2, tb_2)); assume $GoodHeap($h_2);
	$h_2 := $Write($h_2, x, $F, ta_2); assume $GoodHeap($h_2);
	$h_2 := $Write($h_2, x, $G, tb_2); assume $GoodHeap($h_2);
	
	// Is there an allocation strategy that makes $h_1 == $h_2?
	// Yes, any strategy that makes ta_1 == ta_2 && tb_1 == tb_2...

	/*  
	assert (exists a1,a2,a3,a4:int ::
	        (ta_1 == Uf(a1) && tb_1 == Uf(a2) &&
	         ta_2 == Uf(a3) && tb_2 == Uf(a4)) && $Heap#Equal($h_1, $h_2));
	*/
	 
	/*         
	assert (exists a1,a2,a3,a4:int :: 
	         ta_1 == Uf(a1) && tb_1 == Uf(a2) &&
	         ta_2 == Uf(a3) && tb_2 == Uf(a4));
	*/
}

procedure $ProcedureF_1(x:Ref);
       modifies $h_1;
       free ensures $GoodHeap($h_1);
       free ensures $Bigger($h_1, old($h_1));
       free ensures $HeapSucc(old($h_1),$h_1); 

procedure $ProcedureF_2(x:Ref);
       modifies $h_2;
       free ensures $GoodHeap($h_2);
       free ensures $Bigger($h_2, old($h_2)); 
       free ensures $HeapSucc(old($h_2),$h_2);
