Auction
=======

This monitor is based on the example from
[CRV'16](https://crv.liflab.ca/wiki/index.php/Main_Page):

<https://crv.liflab.ca/wiki/index.php/Offline_Team2_Benchmark1>

A monitor for an online auction system. Auctions are created for each item with
a particular reserve price and duration in days. Bids must increase in value,
and cannot occur after the item is sold. An item may not sell before it reaches
the reserve price. An item cannot be bid on or sold once the given number of
days has passed.
