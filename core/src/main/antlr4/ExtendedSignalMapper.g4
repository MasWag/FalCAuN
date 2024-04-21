grammar ExtendedSignalMapper;

@header {
package net.maswag;

import java.util.AbstractMap;
import net.maswag.SignalMapperVisitor;

}

expr
     : atomic
     | left=expr TIMES right=expr
     | left=expr DIV right=expr
     | left=expr PLUS right=expr
     | left=expr MINUS right=expr
     | left=expr MOD right=expr
     | MIN LPAREN expr (COMMA expr)* RPAREN
     | MAX LPAREN expr (COMMA expr)* RPAREN
     | LPAREN expr RPAREN
     | ABS expr
     ;

atomic
       : INPUT LPAREN signalID=NATURAL RPAREN
       | OUTPUT LPAREN signalID=NATURAL RPAREN
       | PREVIOUS_MAX_OUTPUT LPAREN signalID=NATURAL RPAREN
       | PREVIOUS_MIN_OUTPUT LPAREN signalID=NATURAL RPAREN
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
MOD : '%' | 'mod' | 'MOD';
MIN : 'min' | 'MIN';
MAX : 'max' | 'MAX';
COMMA : ',';
NATURAL  : [1-9][0-9]* | '0';
FLOAT : NATURAL '.' [0-9]+;
//([1-9][0-9]*('.'[0-9]+)?) | ('0.'[0-9]+);
LPAREN : '(';
RPAREN : ')';
INPUT : 'input';
OUTPUT : 'signal' | 'output';
PREVIOUS_MIN_OUTPUT : 'previous_min_output';
PREVIOUS_MAX_OUTPUT : 'previous_max_output';
ABS : 'abs' | 'ABS';