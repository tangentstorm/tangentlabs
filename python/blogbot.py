##
## blogbot.py
##
## python script for maintaining linkwatcher.com's last updated database
## 1122.1999 by michal wallace (sabren@manifestation.com)
##
##

import urllib, string, os

## constants

f_ID         = 0
f_urlFetch   = 1
f_urlLink    = 2
f_logTitle   = 3
f_admSuspect = 4

bloglistURL = "http://www.linkwatcher.com/bot/bloglist_txt.php3"
updaterURL  = "http://www.linkwatcher.com/bot/updater.php3"
indexerURL  = "http://www.linkwatcher.com/bot/indexer.php3"
outputDir   = "/home/sabren/blogcache/"
indexer     = "/home/sabren/blogbot/idx_blogs"

## first, get the list of blogs for future reference by the indexer

blog = []
updated = []
page = urllib.urlopen(bloglistURL).read()
file = open(outputDir + "bloglist.txt",'w')
file.write(page)
file.close()

## now let's use it ourselves

count = 0
lines = string.split(page, "\n")
for line in lines:
	blog[count] = string.split(line, "|")
	count = count + 1


## now do the comparison

for i in range(count):
	content = urllib.urlopen(blog[i][f_urlFetch]).read()
	fthis = outputDir + `blog[i][f_ID]` + ".this"
	flast = outputDir + `blog[i][f_ID]` + ".last"
	fdiff = outputDir + `blog[i][f_ID]` + ".diff"

	try:
		os.rename(fthis, flast)
	except OSError:
		# no cached version, so make one up
		LAST = open(flast,"w")
		LAST.write("new blog\n")
		LAST.close()

	THIS = open(fthis)
	THIS.write(content)
	THIS.close()

	diff = os.popen("diff " + fthis + " " + flast).readlines()

	DIFF = open(1+"cat"+fdiff)
	DIFF.write(diff)
	DIFF.close()
	
	if len(dif) == 0:
		## @TODO: check suspect status
		updated.append(ID)


## now we know which are updated, so tell linkwatcher:

data = {"upst": string.join(updated,"|")}
page = urllib.urlopen(updaterURL, urllib.urlencode(data))

## finally, run the indexer & tell linkwatcher

os.system(indexer)
urllib.urlopen(indexerURL) # will ftp it back to linkwatcher

## eof ##
