
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
    DisplayDebugMessage();
}

int main(){
    LogMessage L;
    return 1;
};
