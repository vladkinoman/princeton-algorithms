import edu.princeton.cs.algs4.StdOut;
import edu.princeton.cs.algs4.In;
import edu.princeton.cs.algs4.FlowNetwork;
import edu.princeton.cs.algs4.FlowEdge;
import edu.princeton.cs.algs4.FordFulkerson;
import edu.princeton.cs.algs4.ST;

public class BaseballElimination {
    private FlowNetwork fn;
    private ST<String, Integer[]> st;
    
    /**
     * Create a baseball division from given filename 
     * in format specified below.
     * @param filename name of the file which stores a baseball division
     */
    public BaseballElimination(String filename) {
        In in = new In(filename);
        int n = in.readInt();
        st = new ST<>();
        int teamID = 0;
        while (!in.isEmpty()) {
            String sTeam = in.readString();
            Integer[] aTeamData = new Integer[4+n];
            for (int i = 0; i < aTeamData.length; i++) {
                if (i == 0) {
                    aTeamData[0] = teamID;
                    continue;
                }
                aTeamData[i] = in.readInt();
            }
            st.put(sTeam, aTeamData);
            teamID++;
        }
    }

    
    /**
     * Returns number of teams.
     * @return number of teams
     */
    public int numberOfTeams() {
        return st.size();
    }
    
    /**
     * Returns all teams as an Iterable
     * @return all teams
     */
    public Iterable<String> teams() {
        return st.keys();
    }
    
    private void validateTeam(String team) {
        if (!st.contains(team)) {
            throw new IllegalArgumentException("The team " +
             team + " is not a valid team.");
        }
    }

    /**
     * Returns number of wins for given team.
     * @param team name of the team
     * @return number of wins for given team
     */
    public int wins(String team) {
        validateTeam(team);
        return st.get(team)[1];
    }
    
    /**
     * Returns number of losses for given team.
     * @param team name of the team
     * @return number of losses for given team
     */
    public int losses(String team) {
        validateTeam(team);
        return st.get(team)[2];
    }
    
    /**
     * Returns number of remaining games for given team.
     * @param team name of the team
     * @return number of remaining games for given team
     */
    public int remaining(String team) {
        validateTeam(team);
        return st.get(team)[3];
    }
    
    /**
     * Returns number of remaining games between team1 and team2.
     * @param team1 name of the first team
     * @param team2 name of the second team
     * @return number of remaining games between team1 and team2
     */
    public int against(String team1, String team2) {
        validateTeam(team1);
        validateTeam(team2);
        return st.get(team1)[st.get(team2)[0]];
    }
    
    /**
     * Is given team eliminated?
     * @param team name of the team
     * @return {@code true} if given team eliminated, {code false} otherwise
     */
    public boolean isEliminated(String team) {
        validateTeam(team);
        return false;
    }
    
    /**
     * Returns subset R of teams that eliminates given team;
     *  null if not eliminated.
     * @param team name of the team
     * @return subset R of teams that eliminates given team;
     *  null if not eliminated
     */
    public Iterable<String> certificateOfElimination(String team) {
        validateTeam(team);
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

