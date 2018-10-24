Multiple Moving Averages
========================

Let's say we have a resource shared by a varying number of users. The resource
is limited (say, RAM), so if too many users are using too much, we should raise
an alarm. However, a little transient overuse might be okay (e.g. we *can* swap
but don't want to be constantly swapping) so we keep a moving average for each
user.

There are two monitor types:
* `frontend`
* `averager`

The `frontend` monitors accept incoming `measurement` events that contain two
parameters: an `int consumerID` and a `float usage`. It increments its
measurement count and passes a new event (with the same parameters) to the
`averager`s. This event is a creation event for them, with the
`consumerID` being their ID.

The `averager`s contain 5 floats that they use to store the last 5 measurements.

When the `frontend`'s measurement count reaches 5, it will reset to zero and the
`frontend` will request all the current averages from the `averager`s. If the
sum passes above a threshold, it raises an alarm. If it falls back below the
threshold, it signals everything is normal again.

Sample Data
-----------

Sample input measurements are in the test folder, as well as scripts to send
and receive the messages over RabbitMQ.

* `test_input.json`: The sample data. There are 15 measurements, so the monitor
  will evaluate the total usage three times. The first time everything should
  be fine. The second, it will reach the threshold and trigger an alarm. For
  the final, the average will fall below the threshold again and cause an alarm
  reset.

* `sendJSON.py`: Sends the sample input messages over RabbitMQ.

  Usage: `./sendJSON.py [input_file [message_count]]`

  You can optionally specify the file containing the input messages and only
  send the first `message_count` messages.

* `amqpsend`: binary for sending RabbitMQ messages, used by sendJSON.py

* `consume_smedl.sh`: Receive messages from RabbitMQ and print them on standard
  out. This will receive any SMEDL message, including both input and output
  messages.
