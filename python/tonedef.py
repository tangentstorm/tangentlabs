import sys
import time
from Numeric import *
from pyFMOD import *

SPECSIZE = 512
RECORDRATE = 6000  # i want it as low as possible for best resolution on the FFT bins 
RECORDLEN = RECORDRATE * 5    # 5 seconds at RECORDRATE khz


# just coppied from the c++ recording demo that comes with fsound
FSOUND_SetOutput(FSOUND_OUTPUT_WINMM);
FSOUND_SetMixer(FSOUND_MIXER_QUALITY_AUTODETECT)
FSOUND_Init(RECORDRATE, 64, FSOUND_INIT_ACCURATEVULEVELS)

## select a default recording driver: 
#for i in range(FSOUND_Record_GetNumDrivers()):
#    print "%d - %s\n" % (i+1, FSOUND_Record_GetDriverName(i))
## oh hell just use the default:
FSOUND_Record_SetDriver(0)


# there's another option if you use OSS for output (whatever that is)
sam = FSOUND_Sample_Alloc(FSOUND_UNMANAGED, RECORDLEN, FSOUND_STEREO | FSOUND_16BITS , RECORDRATE, 255, 128, 255);

#FSOUND_Record_StartSample(sam, False)
#while FSOUND_Record_GetPosition() < RECORDLEN:
#    sys.stdout.write("Recording position = %d\r"
#                     % FSOUND_Record_GetPosition())
#    time.sleep(0.05)
#    
#FSOUND_Record_Stop() #	/* it already stopped anyway */


#channel = FSOUND_PlaySound(FSOUND_FREE, sam)
#print "Playing back sound..."

#while FSOUND_IsPlaying(channel):
#    sys.stdout.write("Playback position = %d\r"
#                     % FSOUND_GetCurrentPosition(channel) )
#    time.sleep(0.05)


########################################
print "doing some reverb crap..."

samp1 = sam
FSOUND_Sample_SetMode(samp1, FSOUND_LOOP_NORMAL) # make it a looping sample */
FSOUND_Record_StartSample(samp1, True)

#  Increase this value if the sound sounds corrupted or the time between recording
#  and hearing the result is longer than it should be..
RECORD_DELAY_MS     = 250
RECORD_DELAY_SAMPLES  = (RECORDRATE * RECORD_DELAY_MS / 1000)


# Let the record cursor move forward a little bit first before we try to play it
# (the position jumps in blocks, so any non 0 value will mean 1 block has been recorded)
while not FSOUND_Record_GetPosition():
    time.sleep(0.0001)
    
channel = FSOUND_PlaySound(FSOUND_FREE, samp1)
originalfreq = FSOUND_GetFrequency(channel)

FSOUND_DSP_SetActive(FSOUND_DSP_GetFFTUnit(), True)

import pyFMOD
pyFMOD._FSOUND_DSP_GetSpectrum.restype = POINTER(c_float * 512)

while True: # @TODO: while not keypressed():
    oldrecordpos = 0
    oldplaypos = 0
    playpos = FSOUND_GetCurrentPosition(channel)
    recordpos = FSOUND_Record_GetPosition()

    # NOTE : As the recording and playback frequencies arent guarranteed to be exactly in 
    # sync, we have to adjust the playback frequency to keep the 2 cursors just enough 
    # apart not to overlap. (and sound corrupted)
    # This code tries to keep it inside a reasonable size window just behind the record
    # cursor. ie [........|play window|<-delay->|<-Record cursor.............] 

    MAGIC = 1000
    if (playpos > oldplaypos) and (recordpos > oldrecordpos):
        diff = playpos - recordpos
	if (diff > -RECORD_DELAY_SAMPLES):
            FSOUND_SetFrequency(channel, originalfreq - MAGIC)#;	/* slow it down */
        elif (diff < -(RECORD_DELAY_SAMPLES * 2)):
	    FSOUND_SetFrequency(channel, originalfreq + MAGIC)#	/* speed it up */
	else:
            FSOUND_SetFrequency(channel, originalfreq)
            
    oldplaypos = playpos;
    oldrecordpos = recordpos;

    # spec is a buffer of 512 floats, with bins for frequencies
    # between 0 and RECORDRATE/2 
    spec = FSOUND_DSP_GetSpectrum().contents
    biggest = 0

    # Harmonic Product Spectrum algorithm for pitch detection
    # http://cnx.rice.edu/content/m11714/latest/
    # based on matlab (?) code found here:
    # http://cnx.rice.edu/content/m11716/latest/hps.m

    # the spectrum does an FFT... Because it's limited to 512
    # bins in FMOD, and the top half are well outside the range
    # my vocal cords can produce, I don't care about them. So I
    # go for only the lower ones
    size = 200  # (200 also fit nicely on the screen)

    f_x  = zeros(size, Float)
    for i in range(size):
        f_x[i] = spec[i]

    ## HSP PART 1 - downsampling (compression)
    f_x2 = ones(size, Float)
    f_x3 = ones(size, Float)
    f_x4 = ones(size, Float)
    
    for i in range((len(f_x)-1)/2):
        f_x2[i] = (f_x[2*i] + f_x[(2*i)+1]) /2.0

    for i in range((len(f_x)-2)/3):
        f_x3[i] = (f_x[3*i] + f_x[(3*i)+1] + f_x[(3*i) + 2] )/ 3.0

    for i in range((len(f_x)-3)/4):
        f_x4[i] = (f_x[4*i] + f_x[(4*i)+1] + f_x[(4*i) + 2] + f_x[(4*i) + 3]) / 4.0

    ## HSP PART 2 - multiplication
    assert max(f_x) <= 1.0
    assert max(f_x2) <= 1.0
    assert max(f_x3) <= 1.0
    assert max(f_x4) <= 1.0
    product = f_x * f_x2 #* f_x3 #* f_x4

    ## HSP PART 3
    biggest, index = 0, 0
    for i in range(size):
        if product[i] > biggest:
            biggest = product[i]
            index = i

    freq = index / float(SPECSIZE) * RECORDRATE
    if freq > 600:
        freq = 0
      
#    for i in range(150):
#        sys.stdout.write(str(min( int(product[i]*100), 9 )))
#        if spec[i] > biggest:
#            biggest = i
    sys.stdout.write("--" + str(freq))
    sys.stdout.write("\n")
    #print biggest
    
    
    

FSOUND_StopSound(channel)
FSOUND_Record_Stop()

FSOUND_Sample_Free(samp1)
FSOUND_Close()
