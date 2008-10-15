    public void remove_true_bug(Object o1)
    /*: modifies content
        ensures "content = old content \<setminus> {o1}";
    */
    {
        Node prev = null;
        Node current = first;
        /*: 
          ghost specvar init_nodes :: objset = "first..Node.nodes";
          ghost specvar to_remove :: objset = 
          "{n. n : init_nodes & n..Node.data = o1}";
          ghost specvar desired_nodes :: objset = "init_nodes \<setminus> to_remove";
        */
        while 
            /*: inv "(prev = null -->
                         first = current & 
                         (desired_nodes \<subseteq> current..Node.nodes)) &
                     (prev ~= null --> 
                         first..Node.nodes = desired_nodes) &
                     (ALL n. n : Node & n : Object.alloc & n ~= null & n ~= prev -->
                         n..Node.nodes = {n} Un n..Node.next..Node.nodes) &
                     (null..Node.nodes = {})"
             */
            (current!=null) {
            /*: "current..Node.nodes" := 
                "current..Node.nodes \<setminus> to_remove"; */
            if (current.data==o1) {
                if (prev==null) {
                    // current should have no predecessors
                    first = current.next;
                } else {
                    prev.next = current.next;
                }
                current.next = null;
                //: "current..Node.nodes" := "{}";
            } else {
                prev = current;
            }
            // this does not work with current.next=null done before in one branch:
            current = current.next;
        }
        /*:
          noteThat "first..Node.nodes = desired_nodes";
          assume "False";
        */
    }
