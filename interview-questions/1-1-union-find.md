# Interview Questions: Union–Find

## Social network connectivity

Problem:

Given a social network containing n members and a log file containing m timestamps at which times pairs of members formed friendships, design an algorithm to determine the earliest time at which all members are connected (i.e., every member is a friend of a friend of a friend ... of a friend). Assume that the log file is sorted by timestamp and that friendship is an equivalence relation. The running time of your algorithm should be mlog⁡nm \log nmlogn or better and use extra space proportional to n.

Solution:

0. Create a new object of WeightedQuickUnionUF data type with n elements and set i to 0.
1. If i less than m and there is no file reading error
        then continue to item 2
    else end of algorithm => print error.
2. Union (connect()) two items of the timestamp i.
3. Check whether count of components in data structure is equal 1 (count()).
    If so then end the algorithm => print i-th timestamp
    else go to item 4.
4. Increment i and go to item 2.
