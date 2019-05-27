package org.group_mmm;

public class Main {
    public static void main(String[] args) {
        try {
            SimulinkSUL.start("cd '/Users/calros/Codes/CyVeriA/example'; initAFC", "/Users/calros/breach-1.2.9");
        } catch (Exception e) {
            System.out.println("Matlab Failure");
        }

        System.out.println("Hello World!!");
    }
}
