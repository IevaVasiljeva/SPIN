/*This specification creates a process Sender and a process Receiver. Sender transmits values from 1 to 10 to receiver.
However, values are not transmitted directly - two intermediate processes are used
for this purpose. Both keep track of the total sum of values that they have transmitted.*/

// Max sum is 55 (summing up 1 till 10), therefore a byte is sufficient.
byte transmittedSum1 = 0;
byte transmittedSum2 = 0;
// Channel for communication between Sender and intermediate processes.
chan toIntermediate = [0] of {byte};
// Channel for communication between intermediate processes and Receiver.
chan toReceiver = [0] of {byte};
// For transmitting the numbers from 1 to 10.
byte value = 1;

// Sends the value to the intermediate processes, and then increments the value.
// Continues in this manner till value >10, then breaks.
active proctype Sender() {
	do
	:: value <=10 -> toIntermediate!value;
					 value++;
	:: else -> 		 break;
	od;
}

// An intermediate process that listens for values from Sender, and transmits them on to the Receiver.
active [2] proctype Intermediate() {
	byte valueToTransmit;

	do
		// If less than 10 numbers have been transmitted, keep listening.
		:: value<=10 ->
			toIntermediate?valueToTransmit;
			if
			:: _pid % 2 == 1 -> transmittedSum1 = transmittedSum1 + valueToTransmit;
			:: else -> transmittedSum2 = transmittedSum2 + valueToTransmit;
			fi
			toReceiver!valueToTransmit;
		// Otherwise stop
		:: else -> break;
	od;
}

// Listens for incoming values until 10 values are received.
active proctype Receiver() {
	byte counter = 0;
	byte received;
	do
		// If less than 10 values received, keep listening.
		:: counter<10 ->
			toReceiver?received;
			counter = counter + 1;
		// Otherwise stop.
		:: else -> break;
	od;
}