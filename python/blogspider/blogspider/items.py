# ref http://doc.scrapy.org/topics/items.html

from scrapy.item import Item, Field

class EntryItem(Item):
    """
    A blog entry.
    """
    title = Field()
    date  = Field()
    text  = Field()
    
