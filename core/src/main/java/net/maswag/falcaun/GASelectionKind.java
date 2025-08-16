package net.maswag.falcaun;

/**
 * Enumeration of selection methods used in Genetic Algorithm (GA) equivalence queries.
 * This enum defines the different strategies for selecting individuals from a population
 * during the genetic algorithm process.
 * 
 * <p>Selection methods determine how individuals are chosen for reproduction based on their fitness.
 * Different selection methods can significantly impact the convergence and effectiveness of the GA.</p>
 * 
 * <p>Used by the GA equivalence oracle implementation to specify which selection strategy to use.</p>
 */
public enum GASelectionKind {
    /**
     * Selects the best solution from the population based on fitness.
     * This approach favors exploitation over exploration by always choosing the fittest individuals.
     */
    BestSolution,
    
    /**
     * Tournament selection randomly selects a subset of individuals and chooses the best from that group.
     * This method provides a balance between exploration and exploitation by introducing some randomness
     * while still favoring fitter individuals.
     */
    Tournament
}