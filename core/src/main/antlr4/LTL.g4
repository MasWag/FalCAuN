grammar LTL;

@header {
package net.maswag.falcaun.parser;

import net.maswag.falcaun.parser.LTLListener;
import net.maswag.falcaun.parser.LTLVisitor;
import net.maswag.falcaun.parser.LTLParser;

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
