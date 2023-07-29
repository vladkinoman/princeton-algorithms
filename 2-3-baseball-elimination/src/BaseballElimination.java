import edu.princeton.cs.algs4.StdOut;

public class BaseballElimination {
    
    /**
     * Create a baseball division from given filename 
     * in format specified below.
     * @param filename
     */
    public BaseballElimination(String filename) {

    }
    
    /**
     * Returns number of teams.
     * @return number of teams
     */
    public int numberOfTeams() {
        return 0;
    }
    
    /**
     * Returns all teams as ...
     * @return all teams
     */
    public Iterable<String> teams() {
        return null;
    }
    
    /**
     * Returns number of wins for given team.
     * @param team
     * @return number of wins for given team
     */
    public int wins(String team) {
        return 0;
    }
    
    /**
     * Returns number of losses for given team.
     * @param team
     * @return number of losses for given team
     */
    public int losses(String team) {
        return 0;
    }
    
    /**
     * Returns number of remaining games for given team.
     * @param team
     * @return number of remaining games for given team
     */
    public int remaining(String team) {
        return 0;
    }
    
    /**
     * Returns number of remaining games between team1 and team2.
     * @param team1
     * @param team2
     * @return number of remaining games between team1 and team2
     */
    public int against(String team1, String team2) {
        return 0;
    }
    
    /**
     * Is given team eliminated?
     * @param team
     * @return {@code true} if given team eliminated, {code false} otherwise
     */
    public boolean isEliminated(String team) {
        return false;
    }
    
    /**
     * Returns subset R of teams that eliminates given team;
     *  null if not eliminated.
     * @param team
     * @return subset R of teams that eliminates given team;
     *  null if not eliminated
     */
    public Iterable<String> certificateOfElimination(String team) {
        return null;
    }
    
    public static void main(String[] args) {
        BaseballElimination division = new BaseballElimination(args[0]);
        for (String team : division.teams()) {
            if (division.isEliminated(team)) {
                StdOut.print(team + " is eliminated by the subset R = { ");
                for (String t : division.certificateOfElimination(team)) {
                    StdOut.print(t + " ");
                }
                StdOut.println("}");
            }
            else {
                StdOut.println(team + " is not eliminated");
            }
        }
    }    
}

