package org.group_mmm.examples;

import org.group_mmm.SimulinkVerifier;
import java.io.FileOutputStream;

/**
 * Generates ETF file of AT_S1
 */
public class ATS1ETF {
    public static void main(String[] args) throws Exception {
        final String output = "/tmp/ATS1.etf";
        FileOutputStream stream = new FileOutputStream(output);
        SimulinkVerifier verifier = new SimulinkVerifier();
    }
}