grammar STL;

@header {
package net.maswag.falcaun;

import net.maswag.falcaun.STLListener;
import net.maswag.falcaun.STLVisitor;
import net.maswag.falcaun.STLParser;

}

import AbstractTemporalLogic;

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

INPUT : 'input';
OUTPUT : 'signal' | 'output';