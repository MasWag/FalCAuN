grammar STL;

@header {
package org.group_mmm;

import java.util.AbstractMap;
import org.group_mmm.STLListener;
import org.group_mmm.STLVisitor;
import org.group_mmm.STLParser;

}

expr
     : atomic
     | left=expr AND right=expr
     | left=expr OR right=expr
     | left=expr IMPLY right=expr
     | NOT expr
     | GLOBALLY expr
     | EVENTUALLY expr
     | NEXT expr
     | left=expr UNTIL right=expr
     | GLOBALLY UNDER interval expr
     | EVENTUALLY UNDER interval expr
     | left=expr UNTIL UNDER interval right=expr
     | LPAREN expr RPAREN
     ;

atomic
       : SIGNAL LPAREN signalID=NATURAL RPAREN operator=EQ value
       | SIGNAL LPAREN signalID=NATURAL RPAREN operator=LT value
       | SIGNAL LPAREN signalID=NATURAL RPAREN operator=GT value
       | SIGNAL LPAREN signalID=NATURAL RPAREN operator=NE value
       ;

value
      : MINUS? NATURAL
      | MINUS? FLOAT
      ;

interval
         : LBRACKET left=NATURAL COMMA right=NATURAL RBRACKET;


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
//([1-9][0-9]*('.'[0-9]+)?) | ('0.'[0-9]+);
LPAREN : '(';
RPAREN : ')';
SIGNAL : 'signal';
