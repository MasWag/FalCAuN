grammar STL;

@header {
package net.maswag;

import net.maswag.STLListener;
import net.maswag.STLVisitor;
import net.maswag.STLParser;

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