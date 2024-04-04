grammar STL;

@header {
package net.maswag;

import net.maswag.STLListener;
import net.maswag.STLVisitor;
import net.maswag.STLParser;

}

expr
     : atomic
     | left=expr binaryOperator right=expr
     | unaryOperator expr
     | unaryTemporalOperator UNDER interval expr
     | left=expr binaryTemporalOperator UNDER interval right=expr
     | LPAREN expr RPAREN
     ;

atomic
       : OUTPUT LPAREN signalID=NATURAL RPAREN comparisonOperator value
       | INPUT LPAREN signalID=NATURAL RPAREN comparisonOperator value
       ;

unaryOperator : NOT | NEXT | unaryTemporalOperator;

unaryTemporalOperator : GLOBALLY | EVENTUALLY ;

binaryOperator : AND | OR | IMPLY | binaryTemporalOperator ;

binaryTemporalOperator : UNTIL | RELEASE ;

comparisonOperator : EQ | LT | GT | NE ;

value
      : MINUS? NATURAL
      | MINUS? FLOAT
      ;

// Defines an interval between two natural numbers. We only support closed intervals.
interval
         : LBRACKET left=NATURAL COMMA right=NATURAL RBRACKET;

// Lexer rules for various tokens used in the grammar.
NEWLINE
    : '\r'? '\n' -> skip
    ;

WS
    : (' ' | '\t') -> skip
    ;

UNDER : '_';
LBRACKET : '[';
RBRACKET : ']';
COMMA:  ',';
GLOBALLY : '[]' | 'alw' | 'G';
EVENTUALLY : '<>' | 'ev' | 'F';
UNTIL : 'U';
RELEASE : 'R';
NEXT: 'X';
OR :  '||';
AND :  '&&';
IMPLY :  '->';
NOT :  '!';
EQ :  '==';
NE :  '!=';
LT :  '<';
GT :  '>';
NATURAL  : [1-9][0-9]* | '0';
MINUS : '-';
FLOAT : NATURAL '.' [0-9]+;
LPAREN : '(';
RPAREN : ')';
INPUT : 'input';
OUTPUT : 'signal' | 'output';