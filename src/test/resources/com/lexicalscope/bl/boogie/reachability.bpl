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
const $Alloc:Field bool;

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

/////////////////////////////////////////////////////////////////////////////
// We need a map to keep 
type Map U V;

function $Map#Domain<U, V>(Map U V): [U] bool;
function $Map#Elements<U, V>(Map U V): [U]V;


function $Isomorphic($fuel:Fuel, $h:Heap, $a1:Ref, $a2:Ref) : Map Addr Addr;
// synonym 
axiom (forall $fuel:Fuel, $h:Heap, $a1:Ref, $a2:Ref :: {$Isomorphic($Succ($fuel),$h,$a1,$a2)}
	$Reach($Succ($fuel), $h,$a1,$a2) == $Reach($fuel, $h,$a1,$a2));

