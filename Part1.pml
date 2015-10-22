/*This specification creates a process Sender and a process Receiver. Sender transmits values from 1 to 10 to receiver.
However, values are not transmitted directly - two intermediate processes Intermediate1 and Intermediate2 are used nondeterministically
for this purpose. Both keep track of the total sum of values that they have transmitted.*/

// Max sum is 55 (summing up 1 till 10), therefore a byte is sufficient.
byte transmittedSum1 = 0;
byte transmittedSum2 = 0;
// Channels for communication between Sender and intermediate processes.
chan toIntermediate1 = [10] of {byte};
chan toIntermediate2 = [10] of {byte};
// Channel for communication between intermediate processes and Receiver.
chan toReceiver = [10] of {byte};
// For transmitting the numbers from 1 to 10.
byte value = 1;

// Nondeterministically sends the value to one of the intermediate processes, and then increments the value.
// Continues in this manner till value >10, then breaks.
active proctype Sender() {
	do
	:: value <=10 -> toIntermediate1!value;
					 value++;
	:: value <=10 -> toIntermediate2!value;
					 value++;
	:: else -> 		 break;
	od;
}

// An intermediate process that listens for values from Sender, and transmits them on to the Receiver.
active proctype Intermediate1() {
	// Process keeps track of the total sum of values transmitted.
	transmittedSum1 = 0;
	byte valueToTransmit = 0;

	do
		:: true ->
			toIntermediate1?valueToTransmit;
			transmittedSum1 = transmittedSum1 + valueToTransmit;
			toReceiver!valueToTransmit;
	od;
}

// An intermediate process that listens for values from Sender, and transmits them on to the Receiver.
active proctype Intermediate2() {
	// Process keeps track of the total sum of values transmitted.
	transmittedSum2 = 0;
	byte valueToTransmit = 0;

	do
		:: true ->
			toIntermediate2?valueToTransmit;
			transmittedSum2 = transmittedSum2 + valueToTransmit;
			toReceiver!valueToTransmit;
	od;
}

// Listens for incoming values until 10 values are received.
active proctype Receiver() {
	byte counter = 0;
	byte received = 0;
	do
		// If less than 10 values received, keep listening.
		:: counter<10 ->
			toReceiver?received;
			counter = counter + 1;
		// Otherwise stop.
		:: else -> break;
	od;
}