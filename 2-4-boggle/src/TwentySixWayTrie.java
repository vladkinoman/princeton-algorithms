public class TwentySixWayTrie {
    private static final int R = 26;

    private Node root;      // root of trie
    private int n;          // number of keys in trie

    // R-way trie node
    private static class Node {
        private int score;
        private Node[] next = new Node[R];
    }

   /**
     * Initializes an empty string symbol table.
     */
    public TwentySixWayTrie() {
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
        Node x = get(root, key, 0);
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
        if (d == key.length()) return x;
        char c = key.charAt(d);
        return get(x.next[c-'A'], key, d+1);
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
        else root = put(root, key, score, 0);
    }

    private Node put(Node x, String key, int score, int d) {
        if (x == null) x = new Node();
        if (d == key.length()) {
            if (x.score == 0) n++;
            x.score = score;
            return x;
        }
        char c = key.charAt(d);
        x.next[c-'A'] = put(x.next[c-'A'], key, score, d+1);
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
        return get(root, prefix, 0) != null;
    }
}
