grammar Bl;

multiversion: version+ EOF;
version: (VERSION program);
program: procedure*;
procedure: PROCEDURE id=IDENTIFIER paramsDecl specification block;
paramsDecl: LPAREN (vars+=paramDecl (COMMA vars+=paramDecl)*)? RPAREN;
paramDecl: IDENTIFIER;
specification: readsSpec? modifiesSpec?;
readsSpec: (READS expression SEMI);
modifiesSpec: (MODIFIES expressionSet SEMI);
expressionSet: 
      (expr+=expression) 
	| LCURLY (expr+=expression (COMMA expr+=expression)*)? RCURLY;
block: LCURLY statements RCURLY;
statements: (stmts+=statement)*;
statement:
      CALL id=IDENTIFIER params SEMI                                  #procedureCall
	| lhs=lhsExpression ASSIGN rhs=rhsExpression SEMI                 #assignment
	| IF LPAREN bexpression RPAREN then=block (ELSE elsethen=block)?  #conditional;
updateRhs: 
	  expr=expression   #expressionUpdate
	| NEW LPAREN RPAREN #allocateUpdate;
params: LPAREN (vars+=param (COMMA vars+=param)*)? RPAREN;
param: IDENTIFIER;	
expression: 
      local=IDENTIFIER           #localRead
    | path                       #heapRead
    | NULL                       #nullConst;

lhsExpression: localLhs|localRootedLhs|pathRootedLhs;
localLhs: local=IDENTIFIER;
localRootedLhs: local=IDENTIFIER (DOT field=IDENTIFIER);
pathRootedLhs: readpath=path (DOT field=IDENTIFIER);

rhsExpression: localRhs|pathRhs|allocRhs;
localRhs: local=IDENTIFIER;
pathRhs: readpath=path;
allocRhs: NEW LPAREN RPAREN;

path: local=IDENTIFIER (DOT fields+=IDENTIFIER)+;
bexpression:
	  lhs=expression '==' rhs=expression # equality
	| lhs=expression '!=' rhs=expression # inequality;

PROCEDURE : 'procedure';
MODIFIES  : 'modifies';
READS     : 'reads';
NEW       : 'new';
CALL      : 'call';
IF        : 'if';
ELSE      : 'else';
NULL      : 'null';
VERSION       : 'VERSION';
LPAREN  : '(';
RPAREN  : ')';
LCURLY  : '{';
RCURLY  : '}';
LSQUARE : '[';
RSQUARE : ']';
COMMA   : ',';
DOT     : '.';
ASSIGN  : ':=';
SEMI    : ';';
IDENTIFIER   : [A-Za-z][A-Za-z0-9]*;
WS           : [ \n\t\r]+ -> channel(HIDDEN);
LINE_COMMENT : '//' ~[\r\n]* -> channel(HIDDEN);
COMMENT      : '/*' .*? '*/' -> channel(HIDDEN);