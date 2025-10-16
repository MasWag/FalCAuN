grammar ExtendedSignalMapper;

@header {
package net.maswag.falcaun;

import java.util.AbstractMap;
import net.maswag.falcaun.SignalMapperVisitor;

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
     | PREVIOUS_MAX extended_expr
     | PREVIOUS_MIN extended_expr
     ;

atomic
       : INPUT LPAREN signalID=NATURAL RPAREN
       | OUTPUT LPAREN signalID=NATURAL RPAREN
       | PREVIOUS_MAX_OUTPUT LPAREN signalID=NATURAL RPAREN
       | PREVIOUS_MIN_OUTPUT LPAREN signalID=NATURAL RPAREN
       | value
       ;

extended_expr
     : OUTPUT LPAREN signalID=NATURAL RPAREN
     | leftv=value TIMES right=extended_expr
     | leftv=value DIV right=extended_expr
     | leftv=value PLUS right=extended_expr
     | leftv=value MINUS right=extended_expr
     | leftv=value MOD right=extended_expr
     | left=extended_expr TIMES rightv=value
     | left=extended_expr DIV rightv=value
     | left=extended_expr PLUS rightv=value
     | left=extended_expr MINUS rightv=value
     | left=extended_expr MOD rightv=value
     | left=extended_expr TIMES right=extended_expr
     | left=extended_expr DIV right=extended_expr
     | left=extended_expr PLUS right=extended_expr
     | left=extended_expr MINUS right=extended_expr
     | left=extended_expr MOD right=extended_expr
     | MIN LPAREN left=extended_expr COMMA right=extended_expr RPAREN
     | MAX LPAREN left=extended_expr COMMA right=extended_expr RPAREN
     | LPAREN extended_expr RPAREN
     | ABS extended_expr
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
PREVIOUS_MIN : 'previous_min';
PREVIOUS_MAX : 'previous_max';
ABS : 'abs' | 'ABS';
