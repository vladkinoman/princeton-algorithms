import edu.princeton.cs.algs4.StdOut;
import edu.princeton.cs.algs4.In;
import edu.princeton.cs.algs4.FlowNetwork;
import edu.princeton.cs.algs4.FlowEdge;
import edu.princeton.cs.algs4.FordFulkerson;
import edu.princeton.cs.algs4.ST;
import edu.princeton.cs.algs4.SET;

/**
 * The {@code BaseballElimination} represents a data type for determining which
 * teams have been mathematically eliminated from winning their division. It 
 * finds those teams for given standings in a sports division at some point
 * during the season. 
 * 
 * <p>
 * This implementation runs Ford-Fulkerson's algorithm which computes maxflow
 * and minimum cut to determine whether the team x is mathematically eliminated.
 * Remember that the team not eliminated iff all edges pointing from s are full
 * in maxflow. Use the {@code certificateOfElimination()} method to get
 * the subset of teams R that eliminate the team x.
 * 
 * @author Vlad Beklenyshchev aka vladkinoman
 */
public class BaseballElimination {
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
        return st.get(team1)[4+st.get(team2)[0]];
    }
    
    /**
     * Is given team eliminated?
     * @param team name of the team
     * @return {@code true} if given team eliminated, {code false} otherwise
     */
    public boolean isEliminated(String team) {
        validateTeam(team);
        for (String other : teams()) {
            if (other.equals(team)) continue;
            if (wins(team) + remaining(team) - wins(other) < 0) return true;
        }
        
        return certificateOfElimination(team) != null;
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
        int n = st.size();
        int s = 0;
        int games = n*n/2 - 3*n/2 + 1;
        int teams = n - 1;
        int t = games + teams + 1;
        FlowNetwork fn = new FlowNetwork(t+1);
        
        ST<String, Integer> otherteams = new ST<>();
        
        SET<String> played = new SET<>();
        SET<String> teamConnectedToEnd = new SET<>();
        SET<String> result = null;
        
        for (String other : teams()) {
            if (other.equals(team)) continue;
            if (wins(team) + remaining(team) - wins(other) < 0) {
                if (result == null) result = new SET<>();
                result.add(other);
            }
        }
        
        int i = games + 1;
        for (String other: teams()) {
            if (other.equals(team) || result != null 
                && result.contains(other)) {
                continue;
            }
            otherteams.put(other, i);
            i++;
        }
        i = 1;
        for (String other1 : teams()) {
            if (other1.equals(team) || 
                result != null && result.contains(other1)) {
                continue;
            } 
            for (String other2 : teams()) {
                if (other2.equals(team) || other2.equals(other1) 
                    || played.contains(other2) || result != null 
                    && result.contains(other2)) {
                    continue;
                }
                if (!played.contains(other1)) {
                    fn.addEdge(new FlowEdge(s, i, against(other1, other2)));
                    fn.addEdge(new FlowEdge(i, otherteams.get(other1), 
                        Double.POSITIVE_INFINITY));
                    fn.addEdge(new FlowEdge(i, otherteams.get(other2), 
                        Double.POSITIVE_INFINITY));
                    i++;
                }
            }
            played.add(other1);
            if (!teamConnectedToEnd.contains(other1)) {
                fn.addEdge(new FlowEdge(otherteams.get(other1), t,
                    wins(team) + remaining(team) - wins(other1)));
                teamConnectedToEnd.add(other1);
            }
        }
        
        FordFulkerson maxflow = new FordFulkerson(fn, s, t);
        
        for (String other : otherteams.keys()) {
            if (maxflow.inCut(otherteams.get(other))) {
                if (result == null) result = new SET<>();
                result.add(other);
            }
        }
        return result;
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