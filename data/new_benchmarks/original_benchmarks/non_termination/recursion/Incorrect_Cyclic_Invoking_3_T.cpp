/*
Commit Number: bcdd0fdf80f57545452eb43fee33903fd3849e53
URL: https://github.com/KDE/akonadi/commit/bcdd0fdf80f57545452eb43fee33903fd3849e53
Project Name: akonadi
License: GPL-3.0
termination: TRUE
*/
class QModelIndex{
    bool vd;
    int clm;
public:
    QModelIndex(bool vld, int clmn):vd(vld), clm(clmn){}
    bool isValid(){
        return vd;
    }
    int column(){
        return clm;
    }
};

class EntityTreeModel{
public:
    int getColumnCount();
    int columnCount();
    QModelIndex parent;
    EntityTreeModel(QModelIndex QL): parent(QL){}
};


int EntityTreeModel::getColumnCount(){
    return 1;
}

int EntityTreeModel::columnCount(){
    if (parent.isValid() && parent.column() != 0 )
        return 0;
    return getColumnCount();
}
int main(){
    QModelIndex QL(true,  0);
    EntityTreeModel E1(QL);
    E1.getColumnCount();
    return 1;

}
