grammar LTL;

@header {
package net.maswag;

import net.maswag.LTLListener;
import net.maswag.LTLVisitor;
import net.maswag.LTLParser;

}

import AbstractTemporalLogic;

expr
     : INPUT EQ ID
     | OUTPUT EQ ID
     | left=expr binaryOperator right=expr
     | unaryOperator expr
     | unaryTemporalOperator UNDER interval expr
     | left=expr binaryTemporalOperator UNDER interval right=expr
     | LPAREN expr RPAREN
     ;

INPUT : 'input';
OUTPUT : 'output';
