
class resolver_query_base {
    enum flags
    {
        canonical_name = 1,
        passive = 2,
        numeric_host = 3,
        numeric_service = 4,
        v4_mapped = 5,
        all_matching = 6,
        address_configured = 7
    };
    friend flags operator ~(flags x){
        return static_cast<flags>(static_cast<unsigned int>(~x));
    }

public:
    void induce(){
        flags a;
        a = canonical_name;
        ~a;
        return;
    }

};


int main(){
    resolver_query_base a;
    a.induce();
    return 0;
}
