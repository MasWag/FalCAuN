grammar SignalMapper;

@header {
package org.group_mmm;

import java.util.AbstractMap;
import org.group_mmm.SignalMapperVisitor;

}

expr
     : atomic
     | left=expr TIMES right=expr
     | left=expr DIV right=expr
     | left=expr PLUS right=expr
     | left=expr MINUS right=expr
     | LPAREN expr RPAREN
     ;

atomic
       : INPUT LPAREN signalID=NATURAL RPAREN
       | OUTPUT LPAREN signalID=NATURAL RPAREN
       | value
       ;

value
      : MINUS? NATURAL
      | MINUS? FLOAT
      ;

NEWLINE
    : '\r'? '\n' -> skip
    ;

WS
    : (' ' | '\t') -> skip
    ;

TIMES : '*';
DIV: '/';
PLUS :  '+';
MINUS : '-';
NATURAL  : [1-9][0-9]* | '0';
FLOAT : NATURAL '.' [0-9]+;
//([1-9][0-9]*('.'[0-9]+)?) | ('0.'[0-9]+);
LPAREN : '(';
RPAREN : ')';
INPUT : 'input';
OUTPUT : 'signal' | 'output';