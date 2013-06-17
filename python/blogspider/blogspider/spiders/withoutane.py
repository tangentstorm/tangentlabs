from scrapy.spider import BaseSpider
from scrapy.selector import HtmlXPathSelector
from scrapy.http import Request
from scrapy.utils.response import get_base_url
from scrapy.utils.url import urljoin_rfc
from blogspider.items import EntryItem

def extract(hxs, path):
    """
    extract a single string value (indicated by the path)
    from ann HtmlXPathSelector
    """
    return ''.join(hxs.select(path).extract())

class WithoutAnESpider(BaseSpider):
    """
    A spider to fetch my old blog off the internet archive.
    """
    name = "withoutane"
    allowed_domains = ["web.archive.org"]
    start_urls = [
        'http://web.archive.org/web/20071013232452/http://www.withoutane.com/' ]
  
    def parse(self, response):
        hxs = HtmlXPathSelector(response)
        for p in hxs.select('//p[@class="archive"]'):
            url = urljoin_rfc(get_base_url(response), extract(p, 'a/@href'))
            if url.endswith('.rnt'):
                print "adding post: ", extract(p, 'a/text()')
                yield Request(url, callback=self.parse_page)

    def parse_page(self, response):
        hxs = HtmlXPathSelector(response)
        for entry in hxs.select('//div[@class="entry"]'):
            yield EntryItem(
                title = extract(entry, 'h1/text()'),
                date  = extract(entry, 'h1/small/text()'),
                text  = extract(entry, '*[name()!="h1"]'))
