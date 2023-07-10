/*
Commit Number: 2a44538e0f43e93257c6d69d0b86d26219dd7a99
URL: https://github.com/qt/qt/commit/2a44538e0f43e93257c6d69d0b86d26219dd7a99
Project Name: qt
License: GNU1.3
termination: TRUE
*/
struct QMetaObject{
	void activate( float sender, int from_signal_index, int to_signal_index, double argv);
	void activate( float sender, int signal_index, double argv);
	void activate( float sender, const QMetaObject *m, int from_local_signal_index, int to_local_signal_index, double argv);
	void activate( float sender, const QMetaObject *m, int local_signal_index, double argv);
};

//1  -> 2
void QMetaObject::activate( float sender, int from_signal_index, int to_signal_index, double argv)
{
    activate(sender, from_signal_index, argv);
}
//2  -> 4
void QMetaObject::activate( float sender, int signal_index, double argv)
{
	const QMetaObject *mo;
	activate(sender, mo , signal_index, argv);
}
// 3 -> 4
void QMetaObject::activate( float sender, const QMetaObject *m, int from_local_signal_index, int to_local_signal_index, double argv)
{
	activate(sender, m, from_local_signal_index, argv);
}
// 4
void QMetaObject::activate( float sender, const QMetaObject *m, int local_signal_index, double argv)
{
	return;
}

int main()
{
	QMetaObject A;
	float sender = 0.2;
	int from_signal_index = 3;
	int to_signal_index = 5;
	double argv = 0.9;
	A.activate( sender, from_signal_index, to_signal_index, argv);
	return 0;
 }

