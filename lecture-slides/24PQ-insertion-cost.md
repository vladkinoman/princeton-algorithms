# PQ insertion cost

> **Insert**. Add node at end, then swim it up.
> **Cost**. At most 1 + lg N compares.

> [Why does it require no more than 1 + logN compares when inserting a new node into a heap?](https://stackoverflow.com/questions/42183035/why-does-it-require-no-more-than-1-logn-compares-when-inserting-a-new-node-int)

Because `log(1) = 0` but inserting into a heap with 1 element takes a comparison

---

This is necessary to account for the border case when the number of notes is 2n. A heap of n levels fits 2n-1 objects, so adding one more object starts the new level:

[![Heap](https://i.stack.imgur.com/roU60.png)](https://i.stack.imgur.com/roU60.png)

Black squares represent seven elements of a three-level heap. Red element is number eight. If your search takes you to the location of this last element, you end up with four comparisons, even though log28 is three.

> thanks for your answer But I don't understand why there are 4 comparisons. For me, it seems only 3 times even if the new added red square swims up to root (three comparisons: red line, green line and blue line, 3 times in total)
>
> >  You need to compare to the root, root's child, root's grandchild, and the red node itself, to ensure that you have found the item that you are looking for.