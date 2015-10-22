/*This specification creates N processes that all want to print infinitely often, and makes sure that only one process at a time is actually printing.*/

// A constant defining the number of processes.
#define N 10
// Array holding information of which processes are printing.
bool print[N] = false;
// Shows how many processes are about to go into the critical printing section.
byte numOfAboutToPrint = 0;
// Number of processes that are actually printing.
byte numOfPrintingP = 0;

int count = 0;

// Process that prints whenever it is the only one that is "about to print".
// It registers the fact that it is printing in the boolean print array and counts the number of processes currently printing.
active [N] proctype Pi() {
	// Process always wants to print, there is no way to leave this loop.
	do
	// Increment the counter to show that process is about to print.
	:: true ->  numOfAboutToPrint++;
				// If the process is the only one that is about to print, let it print.
				if
				:: numOfAboutToPrint==1 ->
										// Record the fact that the process is printing and print.
										print[_pid] = true;
										printf("Process %d is printing!\n", _pid);

										count++;

										// Count the number of processes printing.
										byte j = 0;
										do
										:: j <= N-1 -> if
														:: print[j] -> numOfPrintingP++;
														:: else -> skip;
													   fi
													   j++;
										:: else -> break;
										od

										// Exit the critical section and show it by decrementing the counters.
										print[_pid] = false;
										numOfPrintingP--;
										numOfAboutToPrint--;
				// If there are too many processes about to print, decrement the counter and try again.
				:: numOfAboutToPrint!=1 -> numOfAboutToPrint--;
				fi;
	:: true -> bit z = 0;
				z = z + 1;
	:: true -> bit y = 0;
				y = y+1;
	od;

}

// It should never be the case that more than one process is printing, never claim checks for that.
// If the condition holds, the loop is broken, and never claim terminates resulting in an error.
never {
	do
	:: numOfPrintingP>1 -> break;
	:: else
	od
}