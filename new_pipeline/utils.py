
class Node:  
    def __init__(self, data):  
        self.data = data  
        self.children = []  
        self.parent = None  
    
    def __repr__(self):
        return "Node({})".format(self.data)
    
    def __str__(self):
        return (self.data)

    def add_child(self, child):  
        child.parent = self  
        self.children.append(child)  
  
    def path_to_root(self):  
        path = [self.data]  
        node = self.parent  
        while node is not None:  
            path.append(node.data)  
            node = node.parent  
        return path[::-1]  
  
    def path_from_root(self):  
        return self.path_to_root()[::-1]  
  
    def pretty_print(self, indent=0):  
        print(" " * indent + str(self.data))  
        for child in self.children:  
            child.pretty_print(indent + 2)  

class ConvTree:
    def __init__(self, root):
        self.root = root

    def __repr__(self):
        # str of the entire tree
        raise NotImplementedError

    def get_latest(self) -> list[Node]:
        leaves = []
        def get_leaves_helper(node):
            if len(node.children) == 0:
                leaves.append(node)
            else:
                for child in node.children:
                    get_leaves_helper(child)
        get_leaves_helper(self.root)
        return leaves
    
    def get_conversation(self, leaf):
        return leaf.path_to_root()
    
    def get_full_tree(self):
        if len(self.root.children) == 0:
            return {0: [self.root]}

        level = 0
        res = {level: [self.root]}
        while True:
            level += 1
            res[level] = []
            for node in res[level-1]:
                res[level].extend(node.children)
            if len(res[level]) == 0:
                res.pop(level)
                break
        return_res = []
        for level in res:
            return_res.append([node.data for node in res[level]])
        return return_res

