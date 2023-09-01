#define NDEBUG 1;
class LogMessage{
public:
    ~LogMessage();
};
void MessageBoxW(){
    LogMessage L;
    return;
    }
void DisplayDebugMessage(){
    MessageBoxW();
    return;
}

LogMessage::~LogMessage() {
#ifndef NDEBUG
    DisplayDebugMessage();
#endif
}

int main(){
    LogMessage L;
    return 1;
};
