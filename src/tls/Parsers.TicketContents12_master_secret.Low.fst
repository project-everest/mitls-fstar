module Parsers.TicketContents12_master_secret.Low
open Parsers.TicketContents12_master_secret

friend Parsers.TicketContents12_master_secret

module LP = LowParse.Low

let write_ticketContents12_master_secret = 
  LP.write_flbytes 48ul
