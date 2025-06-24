STL
===

In FalCAuN, signal temporal logic (STL) is used to specify the tested property. The following shows the syntax of STL in FalCAuN.

```
expr : atomic
     | expr && expr
     | expr || expr
     | expr -> expr
     | ! expr
     | GLOBALLY expr
     | GLOBALLY _ INTERVAL expr
     | EVENTUALLY expr
     | EVENTUALLY _ INTERVAL expr
     | X expr
     | expr U expr
     | expr U _ INTERVAL expr
     | ( expr )

atomic : signal(NATURAL) == value
       | signal(NATURAL) < value
       | signal(NATURAL) > value
       | signal(NATURAL) != value
       | input(NATURAL) == value
       | input(NATURAL) < value
       | input(NATURAL) > value
       | input(NATURAL) != value
       | output(NATURAL) == value
       | output(NATURAL) < value
       | output(NATURAL) > value
       | output(NATURAL) != value

value : -? NATURAL | -? FLOAT

GLOBALLY : '[]' | 'alw' | 'G'

EVENTUALLY : '<>' | 'ev' | 'F'

INTERVAL : [ NATURAL , NATURAL ]
```
