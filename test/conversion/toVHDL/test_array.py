'''
Created on 8 Sep 2015

@author: JosyJosy
'''

from __future__ import print_function

# optional import to mark 'xfail' tests
import py.test

import myhdl


def array_1(clk, reset, D, Q):
    ''' testing a 1-dimensional Array
        just making a simple pipeline
    '''
    pl = myhdl.Array( (5,), myhdl.Signal( myhdl.intbv(0)[len(D):]))
    
    @myhdl.always_comb
    def rtlcomb():
        Q.next = pl[4]  
    
    @myhdl.always_seq( clk.posedge, reset = reset)
    def rtlreg():
        pl[1:].next = pl[:4]
        pl[0].next = D
        
    return rtlcomb, rtlreg


def test_array_1():
    clk = myhdl.Signal( bool( 0 ))
    reset = myhdl.ResetSignal( 0, active = 1, async = True)
    D, Q = [myhdl.Signal( myhdl.intbv(0)[8:]) for _ in range(2)]

    assert myhdl.conversion.analyze(array_1, clk, reset, D, Q ) == 0


def tb_array_1():
    
    clk = myhdl.Signal( bool( 0 ))
    reset = myhdl.ResetSignal( 0, active = 1, async = True)
    D, Q = [myhdl.Signal( myhdl.intbv(0)[8:]) for _ in range(2)]

    tbdut = array_1(clk, reset, D, Q )
    
    tCK = 10
    RESETLENGTH = 3
    @myhdl.instance
    def genclkreset():
        reset.next = 1
        clk.next = 1
        yield myhdl.delay( int( tCK // 2 ))
        clk.next = 0
        for i in range(RESETLENGTH):
            yield myhdl.delay( int( tCK // 2 ))
            clk.next = 1
            yield myhdl.delay( tCK - int( tCK // 2 ))
            clk.next = 0
        reset.next = 0
        yield myhdl.delay( int( tCK // 2 ))
        while True:
            clk.next = 1
            yield myhdl.delay( int( tCK // 2 ))
            clk.next = 0
            yield myhdl.delay( tCK - int( tCK // 2 ))
        
    @myhdl.instance
    def stimulus():
        D.next = 0
        idxin = 1
        idxout = 1
        for i in range(5):
            yield clk.posedge
            
        yield myhdl.delay( int( tCK // 4 ))
        
        for i in range( 5 ):
            D.next = idxin
            idxin += 1
            yield clk.posedge
            yield myhdl.delay( int( tCK // 4 ))
            
        for i in range( 10 ):
            D.next = idxin
            idxin += 1
            yield clk.posedge
            print( Q )
            assert Q == idxout
            idxout += 1
            yield myhdl.delay( int( tCK // 4 ))
            
        raise myhdl.StopSimulation

    
    return tbdut, genclkreset, stimulus


def test_tb_array_1():
    assert myhdl.conversion.verify( tb_array_1 ) == 0
    


def array_2(clk, reset, D, Q):
    ''' testing a 2-dimensional Array
        just making a simple pipeline
    '''
    mt = myhdl.Array( (4, 3,), myhdl.Signal( myhdl.intbv(0)[len(D):]))
    
    @myhdl.always_comb
    def rtlcomb():
        Q.next = mt[3][2]
      
    @myhdl.always_seq( clk.posedge, reset = reset)
    def rtlreg():
        mt[0][0].next = D
        mt[0][1:].next = mt[0][:2]
        for i in range(1,4):
            mt[i][0].next = mt[i-1][2]
            mt[i][1:].next = mt[i][:2]
    
    return rtlcomb, rtlreg


def test_array_2():
    clk = myhdl.Signal( bool( 0 ))
    reset = myhdl.ResetSignal( 0, active = 1, async = True)
    D, Q = [myhdl.Signal( myhdl.intbv(0)[8:]) for _ in range(2)]

    assert myhdl.conversion.analyze(array_2, clk, reset, D, Q ) == 0


def tb_array_2():
    
    clk = myhdl.Signal( bool( 0 ))
    reset = myhdl.ResetSignal( 0, active = 1, async = True)
    D, Q = [myhdl.Signal( myhdl.intbv(0)[8:]) for _ in range(2)]

    tbdut = array_2(clk, reset, D, Q )
    
    tCK = 10
    RESETLENGTH = 35
    
    @myhdl.instance
    def genreset():   
        reset.next = 1
        yield myhdl.delay( RESETLENGTH )
        reset.next = 0
        
    @myhdl.instance
    def genclk():
        while True:
            clk.next = 1
            yield myhdl.delay( int( tCK // 2 ))
            clk.next = 0
            yield myhdl.delay( tCK - int( tCK // 2 ))
        
    @myhdl.instance
    def stimulus():
        D.next = 0
        idxin = 1
        idxout = 1
        for i in range(5):
            yield clk.posedge
            
        yield myhdl.delay( int( tCK // 4 ))
        
        for i in range( 12 ):
            D.next = idxin
            idxin += 1
            yield clk.posedge
            yield myhdl.delay( int( tCK // 4 ))
        
        for i in range( 16 ):
            D.next = idxin
            idxin += 1
            yield clk.posedge
            print( Q )    
            assert Q == idxout
            idxout += 1
            yield myhdl.delay( int( tCK // 4 ))
            
        raise myhdl.StopSimulation

    
    return tbdut, genreset, genclk, stimulus


def test_tb_array_2():
    assert myhdl.conversion.verify( tb_array_2 ) == 0
    
    
    
def array_3(clk, reset, Sel1, Sel2, Q):
    ''' testing a 2-dimensional Constant Array
    '''
    aoc = myhdl.Array( [[1,2,3], [4,5,6], [7,8,9]],  myhdl.intbv(0)[len(Q):])
      
    @myhdl.always_seq( clk.posedge, reset = reset)
    def rtlreg():
        Q.next = aoc[Sel2][Sel1]
       
    return rtlreg


def test_array_3():
    clk   = myhdl.Signal( bool( 0 ))
    reset = myhdl.ResetSignal( 0, active = 1, async = True)
    Sel1  = myhdl.Signal( myhdl.intbv(0)[2:])
    Sel2  = myhdl.Signal( myhdl.intbv(0)[2:])
    Q     = myhdl.Signal( myhdl.intbv(0)[4:])

    assert myhdl.conversion.analyze(array_3, clk, reset, Sel1, Sel2, Q ) == 0


def tb_array_3():
    
    clk   = myhdl.Signal( bool( 0 ))
    reset = myhdl.ResetSignal( 0, active = 1, async = True)
    Sel1  = myhdl.Signal( myhdl.intbv(0)[2:])
    Sel2  = myhdl.Signal( myhdl.intbv(0)[2:])
    Q     = myhdl.Signal( myhdl.intbv(0)[4:])

    tbdut = array_3(clk, reset, Sel1, Sel2, Q )
    
    tCK = 10
    RESETLENGTH = 35
    
    @myhdl.instance
    def genreset():   
        reset.next = 1
        yield myhdl.delay( RESETLENGTH )
        reset.next = 0
        
    @myhdl.instance
    def genclk():
        while True:
            clk.next = 1
            yield myhdl.delay( int( tCK // 2 ))
            clk.next = 0
            yield myhdl.delay( tCK - int( tCK // 2 ))
        
    @myhdl.instance
    def stimulus():
        Sel1.next = 2
        Sel2.next = 2
        for i in range(8):
            yield clk.posedge
            
        yield myhdl.delay( int( tCK // 4 ))
        
        for j in range( 3 ):  
            Sel2.next= j         
            for i in range( 3 ):
                Sel1.next = i
                yield clk.posedge
                yield myhdl.delay(0) # need this one for a strange reason???
                print( Q )    
                assert Q == 1 + j * 3 + i
                yield myhdl.delay( int( tCK // 4 ))
            
        raise myhdl.StopSimulation

    
    return tbdut, genreset, genclk, stimulus


def test_tb_array_3():
    assert myhdl.conversion.verify( tb_array_3 ) == 0
    
if __name__ == '__main__':
    myhdl.Simulation( myhdl.traceSignals( tb_array_2)).run()
#     myhdl.Simulation( myhdl.traceSignals( tb_array_3)).run()
    