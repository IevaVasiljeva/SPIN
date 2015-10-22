/*This specification creates N processes that all want to print infinitely often, and makes sure that only one process at a time is actually printing.*/

// A constant defining the number of processes.
#define N 10
// Array holding information of which processes are printing.
bool print[N] = false;
// Channel for communication between processes.
chan canPrint = [0] of {byte};
// Number of processes printing at each moment.
byte numOfPrintingP = 0;

// Process is prompted to print when it receives message.
// It registers the fact that it is printing in the boolean print array, counts the number of processes currently printing and sends a message thus enabling other processes to print.
active [N] proctype Pi() {

	// Process with pid 0 will send the first message. The value of what is sent is not important (but restricted to a bit to minimise space consumption).
	if
	:: _pid == 0 -> canPrint!1;
	:: else -> skip;
	fi

	// Simply for reading.
	bit x = 0;
	// Index used to count the number of processes that are printing.
	byte j = 0;

	// Always listen for incoming messages, and once a message is received, print.
	do
	:: true ->  canPrint?x;
				// Register the fact that this process is printing
				print[_pid] = true;

				// Count how many processes are printing by looping through the array.
				j = 0;
				numOfPrintingP = 0;
				do
				::  j <= N-1 ->
							if
							:: print[j] -> numOfPrintingP++;
							:: else -> skip;
							fi
							j++;
				:: else -> break;
				od

				// Printing is critical, only one process should print at a time.
				printf("Process %d is printing!\n", _pid);

				// Stop printing and send the message to print to another process.
				print[_pid] = false;
				canPrint!1;
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