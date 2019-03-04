
public class WAVLTree {

	private WAVLNode root;
	private WAVLNode EXTNode;

	public WAVLTree() {
		EXTNode = new WAVLNode(-1, null);
		this.root = EXTNode;
	}

	/**
	 * public boolean empty() returns true if and only if the tree is empty
	 */
	public boolean empty() {
		if (this.root == EXTNode) {
			return true;
		}
		return false;
	}

	/**
	 * public String search(int k)
	 *
	 * returns the info of an item with key k if it exists in the tree otherwise,
	 * returns null
	 */
	public String search(int k) {
		if (this.empty()) {
			return null;
		}
		return recSearch(this.root, k);
	}

	/**
	 * @param node
	 * @param k
	 * @return the value of the child (in the sub tree of node) with
	 *         node.getKey()==k if it exists. otherwise, $ret false
	 * 
	 *         acts as binary search
	 */
	private String recSearch(WAVLNode node, int k) {
		if (node.getKey() == -1 || node.getKey() == k) {
			return node.getValue();
		}
		if (node.getKey() < k) {
			return recSearch(node.getRight(), k);
		}
		return recSearch(node.getLeft(), k);
	}

	/**
	 * public int insert(int k, String i)
	 *
	 * inserts an item with key k and info i to the WAVL tree. the tree must remain
	 * valid (keep its invariants). returns the number of rebalancing operations, or
	 * 0 if no rebalancing operations were necessary. returns -1 if an item with key
	 * k already exists in the tree.
	 */
	public int insert(int k, String i) {
		// initializes the node with key k and value i
		WAVLNode input = new WAVLNode(k, i);
		input.right = EXTNode;
		input.left = EXTNode;

		if (empty()) {
			this.root = input;
			return 0;
		}
		WAVLNode y = findActionNode(k); // finds parent node (y)
		if (y.key == k) {
			return -1;
		}
		input.parent = y;
		setSizes(y, 1); // updates the sizes of all nodes in the path from x to the root
		int count; // counts the number of rebalancing actions made (promotes+demotes+rotations)

		if (!this.isLeaf(y)) { // unary node does not require rebalancing
			if (k < y.key) {
				y.left = input;
			} else {
				y.right = input;
			}
			return 0;
		}
		if (k < y.key) {
			y.left = input;
		} else {
			y.right = input;
		}
		count = promote(y);
		count += this.rebalanceInsert(y); // move the problem upwards
		return count;
	}

	/**
	 * public int delete(int k)
	 *
	 * deletes an item with key k from the binary tree, if it is there; the tree
	 * must remain valid (keep its invariants). returns the number of rebalancing
	 * operations, or 0 if no rebalancing operations were needed. returns -1 if an
	 * item with key k was not found in the tree.
	 */
	public int delete(int k) {
		if (this.empty()) { // there isn't any node to delete if the tree is empty
			return -1;
		}
		WAVLNode x = findActionNode(k); // get node with key k
		//x.key != k means that there isn't node with key k to delete in this tree
		if (x.key != k || k == -1) { // k == -1 implies an EXTNode.
			return -1;
		}
		if (isBinary(x)) {
			return deleteBinaryNode(x);
		}
		if (!isLeaf(x)) { // the node x is not binary and not a leaf, therefore it is unary
			return deleteUnaryNode(x);
		}
		// if got here, x is a leaf
		return deleteLeaf(x);
	}

	/**
	 * @pre x is binary
	 * 
	 * @param x - node to delete
	 * @return number of rebalancing actions taken
	 */
	private int deleteBinaryNode(WAVLNode x) {
		WAVLNode y = getSuccessor(x); // after the deletion, x is replaced by y
		WAVLNode temp = y; // a pointer to y to keep it after it's deletion
		int count = delete(y.key); // number of rebalancing actions taken
		int k = x.key;

		// update the fields of y so it replaces x
		if (x.right != EXTNode) {
			x.right.parent = temp;
		}
		if (x.left != EXTNode) {
			x.left.parent = temp;
		}
		temp.rank = x.rank;
		temp.size = x.size;
		temp.right = x.right;
		temp.left = x.left;

		temp.parent = x.parent;
		if (x == this.root) {
			this.root = temp;
		} else {
			if (k < temp.parent.key) {
				temp.parent.left = temp;
			} else {
				temp.parent.right = temp;
			}
		}
		return count;
	}

	/**
	 * @pre x is an unary node
	 * 
	 * @param x - node to delete
	 * @return number of rebalancing actions taken
	 */
	private int deleteUnaryNode(WAVLNode x) {
		int count = 0; //counts the number of rebalancing actions taken
		//updates the sizes of all nodes in the path from x to the root
		setSizes(x.parent, -1);

		if (this.root == x) { // if x is the root, replace the root as needed
			if (x.left == EXTNode) {
				this.root = x.right;
			}
			if (x.right == EXTNode) {
				this.root = x.left;
			}
			this.root.parent = null;
		} else { // x is inner unary node
			if (x.right != EXTNode) { //x has only right child
				x.right.parent = x.parent;
				if (x.parent.right == x) {
					x.parent.right = x.right;
				} else {
					x.parent.left = x.right;
				}
			} else { //x has only left child
				x.left.parent = x.parent;
				if (x.parent.right == x) {
					x.parent.right = x.left;
				} else {
					x.parent.left = x.left;
				}
			}
			count = rebalanceDelete(x.parent); // move the problem upwards
		}
		return count;
	}

	/**
	 * @pre x is a leaf
	 * @param x - node to delete
	 * @return number of rebalancing actions taken
	 */
	private int deleteLeaf(WAVLNode x) {
		int count = 0; // counts the number of rebalancing actions taken
		if (this.root == x) { //delete the root so the tree is empty
			this.root = EXTNode;
		} else {
			//updates the sizes of all nodes in the path from x to the root
			setSizes(x.parent, -1);
			
			if (x.parent.right == x) {
				x.parent.right = EXTNode;
			} else {
				x.parent.left = EXTNode;
			}
			count = rebalanceDelete(x.parent); // move the problem upwards
		}
		return count;
	}

	/**
	 * @param node - node to check
	 * @return true if node has two children. otherwise, returns false
	 */
	private boolean isBinary(WAVLNode node) {
		return (node.right != EXTNode && node.left != EXTNode);
	}

	/**
	 * @pre node is in a WAVL tree
	 * @param node - node to check
	 * @return
	 */
	private boolean isLeaf(WAVLNode node) {
		if (node.right == EXTNode && node.left == EXTNode) {
			return true;
		}
		return false;
	}

	/**
	 * @param y - the node to return it's successor
	 * @return the node with the succeeding key. if there isn't one, returns null
	 */
	private WAVLNode getSuccessor(WAVLNode y) {
		// search for node with the smallest key in the subtree of right child
		if (y.right.rank != -1) {
			y = y.right;
			while (y.left.rank != -1) {
				y = y.left;
			}
			return y;
		}
		// if there y has no right child,
		// search for the first parent that y is in it's left child subtree
		WAVLNode temp = y.parent;
		while (temp != null && y == temp.right) {
			y = temp;
			temp = y.parent;
		}
		return temp;
	}

	/**
	 * public String min()
	 *
	 * Returns the info of the item with the smallest key in the tree, or null if
	 * the tree is empty
	 */
	public String min() {
		if (this.empty()) {
			return null;
		}
		WAVLNode leftNode = this.root;
		while (leftNode.getLeft() != EXTNode) {
			leftNode = leftNode.getLeft();
		}
		return leftNode.getValue();
	}

	/**
	 * public String max()
	 *
	 * Returns the info of the item with the largest key in the tree, or null if the
	 * tree is empty
	 */
	public String max() {
		if (this.empty()) {
			return null;
		}
		WAVLNode rightNode = this.root;
		while (rightNode.getRight() != EXTNode) {
			rightNode = rightNode.getRight();
		}
		return rightNode.getValue();
	}

	/**
	 * public int[] keysToArray()
	 *
	 * Returns a sorted array which contains all keys in the tree, or an empty array
	 * if the tree is empty.
	 */
	public int[] keysToArray() {
		if (this.empty()) {
			return new int[0];
		}
		// insert all the keys in-order to arr
		int[] arr = new int[this.root.getSubtreeSize()];
		recKeysToArray(this.root, arr, 0);
		return arr;
	}

	/**
	 * @param node
	 * @param arr - the keys array we update during the rec method
	 * @param startFrom indicates from which index in arr we start to insert the
	 *                  following keys of node's sub tree
	 */
	private void recKeysToArray(WAVLNode node, int[] arr, int startFrom) {
		if (node != EXTNode) {
			recKeysToArray(node.getLeft(), arr, startFrom);

			// node's left child sub tree size
			int leftSize = node.getLeft().getSubtreeSize();

			arr[startFrom + leftSize] = node.getKey();
			recKeysToArray(node.getRight(), arr, startFrom + leftSize + 1);
		}
	}

	/**
	 * public String[] infoToArray()
	 *
	 * Returns an array which contains all info in the tree, sorted by their
	 * respective keys, or an empty array if the tree is empty.
	 */
	public String[] infoToArray() {
		if (this.empty()) {
			return new String[0];
		}
		// insert all the values in-order to arr
		String[] arr = new String[this.root.getSubtreeSize()];
		recInfoToArray(this.root, arr, 0);
		return arr;
	}

	/**
	 * @param node
	 * @param arr - the values array we update during the rec method
	 * @param startFrom indicates from which index in arr we should start insert the
	 *                  following values of node's subtree
	 */
	private void recInfoToArray(WAVLNode node, String[] arr, int startFrom) {
		if (node != EXTNode) {
			recInfoToArray(node.getLeft(), arr, startFrom);

			// node's left child sub tree size
			int leftSize = node.getLeft().getSubtreeSize();
			
			arr[startFrom + leftSize] = node.getValue();
			recInfoToArray(node.getRight(), arr, startFrom + leftSize + 1);
		}
	}

	/**
	 * public int size()
	 *
	 * Returns the number of nodes in the tree.
	 */
	public int size() {
		if (this.empty()) {
			return 0;
		}
		return this.root.getSubtreeSize();
	}

	/**
	 * public WAVLNode getRoot()
	 *
	 * Returns the root WAVL node, or null if the tree is empty
	 */
	public WAVLNode getRoot() {
		if(this.empty()) {
			return null;
		}
		return this.root;
	}

	/**
	 * public int select(int i)
	 *
	 * Returns the value of the i'th smallest key (return -1 if tree is empty)
	 * Example 1: select(1) returns the value of the node with minimal key Example
	 * 2: select(size()) returns the value of the node with maximal key Example 3:
	 * select(2) returns the value 2nd smallest minimal node, i.e the value of the
	 * node minimal node's successor
	 */
	public String select(int i) {
		if (empty() || this.root.getSubtreeSize() < i) {
			return null;
		}
		// the i'th smallest node is at index i-1
		return recSelect(this.root, i - 1);
	}

	/**
	 * @param node
	 * @param i
	 * @return the value of the node in index i is in the subtree of 'node'. if there are
	 *         less than i nodes in the subtree of 'node', return null.
	 */
	private String recSelect(WAVLNode node, int i) {
		if (node == EXTNode) {
			return null;
		}
		int s = 0; //the size of the left child subtree - indicates where the i'th node is
		if (node.getLeft() != EXTNode) {
			s = node.getLeft().getSubtreeSize();
		}
		if (i == s) {
			return node.value;
		} else {
			if (i < s) {
				return recSelect(node.getLeft(), i);
			}
		}
		// i is larger than 1+s,
		// therefore it is in the subtree of node's right child
		return recSelect(node.getRight(), i - s - 1);
	}

	/**
	 * @pre this.root != null
	 * @param k
	 * @return node with key k. if there isn't one, returns the insertion point* of a
	 *         node with key k.
	 *         *The insertion point of node x is the node x supposed to be it's child if inserted
	 */
	private WAVLNode findActionNode(int k) {
		return recFindActionNode(this.root, k);
	}
	/**
	 * search for node with key k. works like search method, returns entire 
	 * node instead of only value.
	 * @param node - the node we search in it's subtree for node with key k
	 * @param k 
	 * @return node with key k.
	 */
	private WAVLNode recFindActionNode(WAVLNode node, int k) {
		if (k == node.key) {
			return node;
		}
		if (k < node.key) {
			if (node.left == EXTNode) {
				return node;
			}
			return recFindActionNode(node.left, k);
		}
		if (node.right == EXTNode) {
			return node;
		}
		return recFindActionNode(node.right, k);
	}
	/**
	 * rebalance after insertion. rebalance the tree to be an accurate WAVL tree with 
	 * correct edge differences. rebalance from node y upwards.
	 * @pre y's children subtrees are balanced as an accurate WAVL trees.
	 * 
	 * @param y - the node we start rebalance upwards from
	 * @return number of rebalancing actions taken: promotes+demotes+rotations.
	 */
	private int rebalanceInsert(WAVLNode y) {
		if (this.root == y) {
			return 0; //y was already promoted before the call to rebalanceInsert(y)
		}
		int edgeDiff = y.getParentEdgeDiff();
		
		if (edgeDiff == 1) {//no rotations or moving problems upwards
			return 0;
		}
		int bfParent = y.parent.getBalanceFactor();
		if (edgeDiff == 0) {
			if (bfParent == 1 || bfParent == -1) {
				//set correct rank and move the problem upwards
				return promote(y.parent) + rebalanceInsert(y.parent); 
			}
		}
		// ends the rebalancing actions by rotation as needed
		return this.rotateInsert(y, bfParent, y.getBalanceFactor());
	}
	
	/**
	 * Assisted by the balance factors, making the correct rotations to balance the tree 
	 * after the insertion.
	 * 
	 * @param y - the node it's children subtrees are balanced
	 * @param bfParent - the balance factor of y's parent
	 * @param bfCurrent - the balance factor of y
	 * @return number of rebalancing actions taken: promotes+demotes+rotations.
	 */
	private int rotateInsert(WAVLNode y, int bfParent, int bfCurrent) {
		if (bfParent == 2 && bfCurrent == 1) { //single rotation right
			return rotateRight(y, true);
		}
		if (bfParent == -2 && bfCurrent == -1) { //single rotation left
			return rotateLeft(y, true);
		}
		WAVLNode temp;
		int count; // counts the number of rebalancing actions made
		
		if (bfParent == 2 && bfCurrent == -1) {
			//double rotation on y's right child - left and then right
			//and promote
			temp = y.right;
			count = rotateLeft(temp, true);
			count += rotateRight(temp, true);
			count += promote(temp);
			return count;
		}
		if (bfParent == -2 && bfCurrent == 1) {
			//double rotation on y's left child - right and then left
			//and promote
			temp = y.left;
			count = rotateRight(temp, true);
			count += rotateLeft(temp, true);
			count += promote(temp);
			return count;
		}
		return -100; // should never get here
	}

	/**
	 * rebalance after deletion. rebalance the tree to be a correct WAVL tree with 
	 * correct edge differences. rebalance from node y upwards.
	 * @pre y's children subtrees are balanced as an accurate WAVL trees.
	 * 
	 * @param y - the node we start rebalance upwards from.
	 * @return number of rebalancing actions taken: promotes+demotes+rotations.
	 */
	private int rebalanceDelete(WAVLNode y) {
		if (y == null) {
			return 0;
		}
		int rDiff = y.getChildEdgeDiff('r');
		int lDiff = y.getChildEdgeDiff('l');
		if (lDiff == 2 && rDiff == 2) { //make sure a leaf has rank 0
			if (isLeaf(y)) {
				return demote(y) + rebalanceDelete(y.parent);
			}
			return 0;
		}
		//move the problem upwards
		if ((lDiff == 3 && rDiff == 2) || (lDiff == 2 && rDiff == 3)) {
			return demote(y) + rebalanceDelete(y.parent);
		}
		
		if (lDiff == 3 && rDiff == 1) {
		//the following rebalance depends on the edges of y with it's children
			int lChildDiff = y.right.getChildEdgeDiff('l');
			int rChildDiff = y.right.getChildEdgeDiff('r');
			
			//double demote and move the problem upwards
			if (lChildDiff == 2 && rChildDiff == 2) { 
				return demote(y) + demote(y.right) + rebalanceDelete(y.parent);
			}
			//single rotation of y's right child to the left
			if ((lChildDiff == 2 || lChildDiff == 1) && rChildDiff == 1) {
				return rotateLeft(y.right, false);
			}
			//demote then double rotation of the left child of y's right child - 
			//to the right and then to the left
			if (lChildDiff == 1 && rChildDiff == 2) {
				WAVLNode temp = y.right.left;
				return demote(y) + rotateRight(temp, false) + rotateLeft(temp, false);
			}
		}
		
		if (lDiff == 1 && rDiff == 3) {
			//the following rebalance depends on the edges of y with it's children
			int lChildDiff = y.left.getChildEdgeDiff('l');
			int rChildDiff = y.left.getChildEdgeDiff('r');
			
			//double demote and move the problem upwards
			if (lChildDiff == 2 && rChildDiff == 2) {
				return demote(y) + demote(y.left) + rebalanceDelete(y.parent);
			}
			//single rotation of y's left child to the right
			if (lChildDiff == 1 && (rChildDiff == 1 || rChildDiff == 2)) {
				return rotateRight(y.left, false);
			}
			//demote and then double rotation of the right child of y's left child -
			//to the left and then to the right
			if (lChildDiff == 2 && rChildDiff == 1) {
				WAVLNode temp = y.left.right;
				return demote(y) + rotateLeft(temp, false) + rotateRight(temp, false);
			}
		}
		return 0; //all cases for rebalncing were covered. 
	}
	/**
	 * increase rank of y by 1.
	 * @param y - the node which it's rank will be increased
	 * @return the number of promotes done- if y is inner node 1, otherwise 0.
	 */
	private int promote(WAVLNode y) {
		if (y == EXTNode) {
			return 0;
		}
		y.rank += 1;
		return 1;
	}
	/**
	 * decrease rank of y by 1.
	 * @param y - the node which it's rank will be decreased
	 * @return 1, as the number of demotes done- if y is inner node 1, otherwise 0.
	 */
	private int demote(WAVLNode y) {
		if (y == EXTNode) {
			return 0;
		}
		y.rank -= 1;
		return 1;
	}
	/**
	 * climb on the path from node y to the root of the tree and add i to the sizes of
	 * every node in the path.
	 * @param y - node to start moving upwards from
	 * @param i - added to the sizes.
	 */
	private void setSizes(WAVLNode y, int i) {
		while (y != null) { //stops at the root
			y.size += i;
			y = y.parent;
		}
	}
	/**
	 * rotate the node y to the left - makes it the new root of the subtree.
	 * there is a little difference if the rotation is after deletion (and not insertion),
	 * therefore the boolean isInsert
	 * 
	 * @param y - the node we rotate so it become the new "root" of the subtree.
	 * @param isInsert - indicates if the rotation is a part of insertion - true,
	 * otherwise the rotation is a part of a deletion - false.
	 * @return number of rebalancing actions taken in this rotation: 1 rotate + promotes+demotes
	 */
	private int rotateLeft(WAVLNode y, boolean isInsert) {
		int count; //counts the number of rebalancing actions made
		WAVLNode temp = y.parent;
		y.parent = y.parent.parent;
		if (y.parent == null) {//if the parent of y's parent is the root, now y becomes the root
			this.root = y;
		} else { //set y as a child to it's new parent
			if (y.key < y.parent.key) {
				y.parent.left = y;
			} else {
				y.parent.right = y;
			}
		}
		//sets previous left child of y as the new right child of y's previous parent
		temp.right = y.left;
		temp.right.parent = temp;
		
		//sets y's previous parent as it's left child
		y.left = temp;
		temp.parent = y;
		
		//sets correct sizes after the pass
		int s = 1 + y.right.size; // 1 is for node y
		if (temp.left == EXTNode) {
			y.size += 1;
		} else {
			y.size += temp.left.size + 1;
		}
		temp.size -= s;
		
		//counts 1 rotation that has been done and sets correct ranks
		count = 1 + demote(temp);
		if (!isInsert) { //rotate in deletion
			count += promote(y);//rotate in deletion has another promote
			if (isLeaf(y.left) && y.left.rank != 0) {//make sure a leaf's rank is 0
				count += demote(y.left);
			}
		}
		return count;
	}
	
	/**
	 * rotate the node y to the right - makes it the new root of the subtree.
	 * there is a little difference if the rotation is after deletion (and not insertion),
	 * therefore the boolean isInsert
	 * 
	 * @param y - the node we rotate so it become the new "root" of the subtree.
	 * @param isInsert - indicates if the rotation is a part of insertion - true,
	 * otherwise the rotation is a part of a deletion - false.
	 * @return number of rebalancing actions taken in this rotation: 1 rotate + promotes+demotes
	 */
	private int rotateRight(WAVLNode y, boolean isInsert) {
		int count; //counts the number of rebalancing actions made
		WAVLNode temp = y.parent;
		y.parent = y.parent.parent;
		if (y.parent == null) {//if the parent of y's parent is the root, now y becomes the root
			this.root = y;
		} else { //set y as a child to it's new parent
			if (y.key < y.parent.key) {
				y.parent.left = y;
			} else {
				y.parent.right = y;
			}
		}
		//sets previous left child of y as the new right child of y's previous parent
		temp.left = y.right;
		temp.left.parent = temp;
		
		//sets y's previous parent as it's left child
		y.right = temp;
		temp.parent = y;

		//sets correct sizes after the pass
		int s = 1 + y.left.size; //1 is for node y
		if (temp.right == EXTNode) {
			y.size += 1;
		} else {
			y.size += 1 + temp.right.size;
		}
		temp.size -= s;
		
		//counts 1 rotation that has been done and sets correct ranks
		count = 1 + demote(temp);
		if (!isInsert) { //rotate in deletion
			count += promote(y);//rotate in deletion has another promote
			if (isLeaf(y.right) && y.right.rank != 0) {//make sure a leaf's rank is 0
				count += demote(y.right);
			}
		}
		return count;
	}

	/**
	 * public class WAVLNode
	 */
	public class WAVLNode {
		private String value;
		private int key;
		private WAVLNode parent;
		private WAVLNode right;
		private WAVLNode left;
		private int rank;
		private int size = 1;

		/**
		 * constructor for nodes, receives key and value
		 */
		public WAVLNode(int key, String value) { 
			this.key = key;
			this.value = value;
			if (value == null && key == -1) {
				this.rank = -1;
				this.size = 0;
			}

		}

		public int getKey() {
			return this.key;
		}

		public String getValue() {
			return this.value;
		}

		public WAVLNode getLeft() {
			return this.left;
		}

		public WAVLNode getRight() {
			return this.right;
		}
		/**
		 * inner node is any node that isn't an external node
		 * @return true if this is an inner node. Otherwise, false
		 */
		public boolean isInnerNode() {
			if (this.rank != -1) {
				return true;
			}
			return false;
		}
		/**
		 * @return number of inner nodes in this node's subtree
		 */
		public int getSubtreeSize() {
			return this.size;
		}
		/**
		 * @return if this node has a parent - returns the rank differences between this 
		 * node and it's parent. parent's rank minus this node's rank.
		 * Otherwise, this node is a root (or has no parent) returns -1.
		 */
		public int getParentEdgeDiff() {
			if (this.parent == null) { //this node has no parent
				return -1;
			}
			return this.parent.rank - this.rank;
		}
		/**
		 * 
		 * @param c - indicates which edge $ret will be. 'r' for right edge , otherwise left edge.
		 * @return edge differences between this node and it's right/left child, 
		 * child determined by c 
		 */
		private int getChildEdgeDiff(char c) {
			if (c == 'r') {
				return this.rank - this.right.rank;
			}
			return this.rank - this.left.rank;
		}
		
		/**
		 * balance factor is the difference between
		 * this node's edge with right child to this node's edge with left child.
		 * (right edge minus left edge)
		 * @return balance factor of this node.
		 */
		private int getBalanceFactor() {
			int r, l;
			// get edge diff from right child
			if (this.right == EXTNode) {
				r = this.rank + 1; // rank of null is -1
			} else {
				r = this.right.getParentEdgeDiff();
			}
			// get edge diff from left child
			if (this.left == EXTNode) {
				l = this.rank + 1;
			} else {
				l = this.left.getParentEdgeDiff();
			}
			return r - l;
		}

		public int getRank() {
			return rank;
		}
	}
}
