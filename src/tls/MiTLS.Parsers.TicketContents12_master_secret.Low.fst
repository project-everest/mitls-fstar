module MiTLS.Parsers.TicketContents12_master_secret.Low
open MiTLS
open MiTLS.Parsers.TicketContents12_master_secret

friend MiTLS.Parsers.TicketContents12_master_secret

module LP = LowParse.Low

let write_ticketContents12_master_secret = 
  LP.write_flbytes 48ul
