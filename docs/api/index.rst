SMEDL Programming Interface
===========================

These pages describe how to interface with the generated monitors. Most
programs will only need the information from :doc:`api` and the page for the
chosen asynchronous transport. The :doc:`full_api` page is useful for those who
want a better understanding of how SMEDL monitors work internally or who want
to integrate with the generated code on a deeper level.

.. note::

   Many file names and identifiers in this API contain placeholders for event,
   monitor, and synchronous set names. These placeholders are marked by the use
   of ALLCAPS.

.. toctree::
   :maxdepth: 2
   :caption: Contents:

   api
   rabbitmq
   ros
   full_api
