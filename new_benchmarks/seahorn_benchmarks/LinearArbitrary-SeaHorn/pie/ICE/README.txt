Before you extract the zip archive you need to unblock it.
   > Right click on the .zip file, click "Properties" and in the General tab, "Unblock" it for usage on your machine.

1. Command to learn invariant for a Boogie program using decision tree algorithms:
   > .\Boogie.exe /nologo /noinfer /contractInfer /mlHoudini:dt_penalty /printAssignment /trace <<path to .bpl program>>

   a) The flag /mlHoudini enables decision tree learning.It can be run in 3 modes:dt_simple, dt_entropy and dt_penalty
   b) The flag /printAssignment prints out the learnt invariant at the end of the analysis.
   c) The flag /trace prints the statistics and other useful information pertaining to learning.
IMPORTANT: Please give the above flags in the same order as specified.
	   Also, please run the tool from directory "tool" which has the Boogie and C5 binaries local to it.
  
2. The directory ".\c5 sample data" contains data files on which the C5 learners can be run as is in a passive setting.
   The .data and .names file follow the normal C5 input format. The .implications file contains the implication constraints.
   An entry "x y" in .implications file indicates that there is an implication from the xth sample point in .data file
   to the yth sample point in the .data file.
   For example, the sum1.implications file indicates that there are 2 implications-- <1,2,2> ==> <2,3,2> and
   <1,0,1> ==> <2,1,1>
   The command for running c5_penalty (accordingly c5_simple and c5_entropy) is:
   > .\c5.0.dt_penalty -I 1 -m 1 -f "c5 sample data\sum1"

3. The boogie and c5 binaries have been tested only on Windows x86 platform.

4. If you are getting VCOMP100.dll not found error when Boogie tries to run Z3, 
   then install Microsoft Visual C++ 2010 Redistributable Package (x86) from 
   http://www.microsoft.com/downloads/en/details.aspx?FamilyID=a7b7a05e-6de6-4d3a-a423-37bf0912db84

The accompanying License file is at .\MSPL.txt
