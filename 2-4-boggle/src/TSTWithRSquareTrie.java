public class TSTWithRSquareTrie {
    private static final int R = 26;
    private static final int SQUARE = 2;
    private Node[][] root;  // root of trie
    private int n;          // number of keys in trie

    // R-way trie node
    private static class Node {
        private char c;                        // character
        private Node left, mid, right;         // left, middle, and right subtries
        private int score;                     // value associated with string
    }

   /**
     * Initializes an empty string symbol table.
     */
    public TSTWithRSquareTrie() {
        root = new Node[R][R];
    }

    /**
     * Returns the value associated with the given key.
     * @param key the key
     * @return the value associated with the given key if the key is in the symbol table
     *     and {@code null} if the key is not in the symbol table
     * @throws IllegalArgumentException if {@code key} is {@code null}
     */
    public int get(String key) {
        if (key == null) throw new IllegalArgumentException("argument to get() is null");
        if (key.length() <= SQUARE) {
            return 0;
        }
        Node r = root[key.charAt(0)-'A'][key.charAt(1)-'A'];
        Node x = get(r, key, SQUARE);
        if (x == null) return 0;
        return x.score;
    }

    /**
     * Does this symbol table contain the given key?
     * @param key the key
     * @return {@code true} if this symbol table contains {@code key} and
     *     {@code false} otherwise
     * @throws IllegalArgumentException if {@code key} is {@code null}
     */
    public boolean contains(String key) {
        if (key == null) throw new IllegalArgumentException("argument to contains() is null");
        return get(key) != 0;
    }

    private Node get(Node x, String key, int d) {
        if (x == null) return null;
        char c = key.charAt(d);
        if      (c < x.c)              return get(x.left,  key, d);
        else if (c > x.c)              return get(x.right, key, d);
        else if (d < key.length() - 1) return get(x.mid,   key, d+1);
        else                           return x;
    }

    /**
     * Inserts the key-value pair into the symbol table, overwriting the old value
     * with the new value if the key is already in the symbol table.
     * If the value is {@code null}, this effectively deletes the key from the symbol table.
     * @param key the key
     * @param score the value
     * @throws IllegalArgumentException if {@code key} is {@code null}
     */
    public void put(String key, int score) {
        if (key == null) throw new IllegalArgumentException("first argument to put() is null");
        if (key.length() <= SQUARE) {
            throw new IllegalArgumentException("key must have length >= 3");
        }
        Node r = root[key.charAt(0)-'A'][key.charAt(1)-'A'];
        root[key.charAt(0)-'A'][key.charAt(1)-'A'] = put(r, key, score, SQUARE);
    }

    private Node put(Node x, String key, int score, int d) {
        char c = key.charAt(d);
        if (x == null) {
            x = new Node();
            x.c = c;
        }
        if      (c < x.c)               x.left  = put(x.left,  key, score, d);
        else if (c > x.c)               x.right = put(x.right, key, score, d);
        else if (d < key.length() - 1)  x.mid   = put(x.mid,   key, score, d+1);
        else {
            if (x.score == 0) n++;
            x.score   = score;
        }
        return x;
    }

    /**
     * Returns the number of key-value pairs in this symbol table.
     * @return the number of key-value pairs in this symbol table
     */
    public int size() {
        return n;
    }

    /**
     * Is this symbol table empty?
     * @return {@code true} if this symbol table is empty and {@code false} otherwise
     */
    public boolean isEmpty() {
        return size() == 0;
    }

    /**
     * Checks whether there is a key with the given {@code prefix }.
     * @param prefix the prefix
     * @return {@code true} if such key exists,
     *     {@code false} otherwise
     */
    public boolean hasKeyWithPrefix(String prefix) {
        if (prefix.length() <= SQUARE) {
            throw new IllegalArgumentException("prefix must have length >= 3");
        }
        return get(root[prefix.charAt(0)-'A'][prefix.charAt(1)-'A'],
         prefix, SQUARE) != null;
    }
}
