.org $a08000
.extern bar.table

foo.loop_forever:
.global foo.loop_forever
    bra     foo.loop_forever
    adc     ($42)
    adc.i16 $20
    wdm
.data $ee

foo.zeroes:
.global foo.zeroes
.zero 20
