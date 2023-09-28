/*
Commit Number: 4bfeeb3fa185dfb445a0475c13fc690f6b90b821
URL: https://github.com/htcondor/htcondor/commit/4bfeeb3fa185dfb445a0475c13fc690f6b90b821
Project Name: htcondor
License: Apache-2.0
termination: TRUE
*/
class ClassAdLog{
	public:
	int LookupInTransaction();
};
int ClassAdLog::LookupInTransaction()
{
	return 0;
}

class ClassAdCollection : private ClassAdLog {
	public:
	int LookupInTransaction()
	{
		return ClassAdLog::LookupInTransaction();
	}

};

int main()
{
	ClassAdCollection A;
	int c = A.LookupInTransaction();
	return 0;
}
