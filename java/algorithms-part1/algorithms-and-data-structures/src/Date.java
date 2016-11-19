/**
 * Created by vbekl_000 on 11/19/2016.
 */

/**
 * compares dates to other dates
 * we have to implement Comparable interface if we work with user-defined
 * data types
 */
public class Date implements Comparable<Date>{
    private final int month, day, year;

    public Date(int month, int day, int year) {
        this.month = month;
        this.day = day;
        this.year = year;
    }

    @Override
    public int compareTo(Date o) {
        if (this.month < o.month) return -1;
        if (this.month > o.month) return 1;
        if (this.day < o.day) return -1;
        if (this.day > o.day) return 1;
        if (this.year < o.year) return -1;
        if (this.year > o.year) return 1;
        return 0;
    }
}
