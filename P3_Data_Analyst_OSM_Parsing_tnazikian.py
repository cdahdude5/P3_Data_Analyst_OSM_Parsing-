
# coding: utf-8

# In[ ]:




# In[24]:

import xml.etree.cElementTree as ET
import pprint, collections, os, codecs, re, json
from timeit import Timer
from pymongo import MongoClient, InsertOne
from collections import OrderedDict, defaultdict
import pandas as pd
import numpy as np


ns = ["name","street"]
mapping = {"California:CA"
           "Calif.": "CA",
           "Ci":"Circle",
           "7-11":"7-Eleven",
           "7":"7-Eleven",
           "Eleven":"",
           "Cte":"Court",
           "Mt":"Mount",
           "841-002":"",
           "Tl":"Trail",
           "Plz":"Plaza",
           "Cv":"Cove",
           "Qrc":"Research Center",
           "Trl":"Trail",
           "Sq": "Square",
           "Tr":"Terrace",
           "Pt": "Point",
           "Bl":"Boulevard",
           "E": "East",
           '10': '10',
           "Pl.": "Place",
           "Bl":"Boulevard",
           "pl": "Place",
           "Pl": "Place",
           '3305': '3305',
           '32500': '32500',
           '77A': '77A Avenue',
           '8500': '8500',
           '99': '99',
           'Alley': 'Alley',
           'Ave': 'Avenue',
           'Ave.': 'Avenue',
           'Blvd': 'Boulevard',
           'Broadway': 'Broadway',
           'Bypass': 'Bypass',
           'Centre': 'Centre',
           'Close': 'Close',
           'Crescent': 'Crescent',
           'Diversion': 'Diversion',
           'Dr': 'Drive',
           'Dr.': 'Drive',
           'East': 'East',
           "tgi": "TGI",
           "Tgi":"TGI",
           "Seo":"SEO",
           "2Nd":"2nd",
           'Edmonds': 'Edmonds Street',
           'Gate': 'Gate',
           'Grove': 'Grove',
           'Hastings': 'Hastings Street',
           'Highway': 'Highway',
           'Hwy': 'Highway',
           'Hwy.': 'Highway',
           'Kingsway': 'Kingsway',
           'Mall': 'Mall',
           'Mews': 'Mews',
           'Moncton': 'Moncton Street',
           'North': 'North',
           'Subway': "Subway Sandwiches",
           'Park': 'Park',
           'Pender': 'Pender Street',
           'RD': 'Road',
           'Rd': 'Road',
           'Rd.': 'Road',
           'Road,': 'Road',
           'S.': 'South',
           'Sanders': 'Sanders Street',
           'South': 'South',
           'St': 'Street',
           'St.': 'Street',
           'Street3': 'street',
           'Terminal': 'Terminal',
           'Tsawwassen': 'North Tsawwassen',
           'Vancouver': 'Vancouver',
           'Walk': 'Walk',
           'Way': 'Way',
           'West': 'West',
           'Willingdon': 'Willingdon',
           'Wynd': 'Wynd',
           'av': 'Avenue',
           'road': 'Road',
           'st': 'Street',
           'Road':'Road',
           'rd' : 'Road',
           'Street': 'Street',
           'Avenue': 'Avenue',
           'Drive': 'Drive',
           'Boulevard':'Boulevard',
           'Parkway': 'Parkway',
           'Place': 'Place',
           'Court': 'Court',
           'Trail': 'Trail',
           'Lane': 'Lane',
           "Rd":"Road",
           "Wy": "Way",
           "Ln":"Lane",
           "Ln.":"Lane",
           "ln":"Lane",
           "Ct":"Court",
           "Ct.":"Court",
           "Rw" :"Row",
           "Rw." :"Row",
           "Caf\xe9": "Cafe",
           "Av": "Avenue",
           "W": "West",
           "Gl": "Glen",
           "Wa": "Way",
           "Avnda":"Avenida",
           "Cr": "Circle",
           "S": "South",
           "Ro": "Row",
           "St.": "Street",
           "Kfc": "KFC",
           "Cvs": "CVS",
           "Wk": "Walk",
           "Subway Sandwiches": "Subway",
           "Starbucks Coffee": "Starbucks"
           }

#mapping is convenient if one is already familiar with street names

filename = "C:\Users\Toshiki_Nazikian\Downloads\SD_city.osm"

class Mapparser:
    
    def __init__(self, filename):
        self._rejects = set()  
        self._passed = set()  
        self._prob = set()
        self.filename = filename
        self.format_name = "{0}.json".format(filename)
        self.elem_list = []
        self.data = {}
        self._tags = {}
        self._tags['prob'] = {}
        self.lower = re.compile(r'^([a-z]|_)*$')
        self.lower_colon = re.compile(r'^([a-z]|_)*:([a-z]|_)*$')
        self.filternames = re.compile(r"city$|housename|postcode|cuisine|housenumber|^name$|amenity|st$|st.$|bridge|:street|street|county$|^county$", flags=re.I)
        self.addrnames = re.compile(r"city$|postcode|housenumber|st$|st.$|:street|street|county$|^county$", flags=re.I)
        self.problemchars = re.compile(r'[=\+/&<>;\'"\?%#$@\,\. \t\r\n]')
        self.tigers = re.compile(r"tiger:")
        self.CREATED = [ "version", "changeset", "timestamp", "user", "uid"]
        self.excluded = [ "version", "changeset", "timestamp", "user", "uid", "lat", "lon", "id"]
        self.process_map(filename, pretty=False)
        
    
    
    #maps abbreviations to whole words & returns string        
    def align_name(self, name):
        for i, word in enumerate(name):
            if word in mapping.keys():
                name[i] = mapping[word]
        return (' '.join(name))
        
            
            

    def shape_element(self, element):
        node = {}
        if element.tag == "node" or element.tag == "way":
            node["pos"] = {}
            try:
                node["pos"]["lon"] = float(element.attrib["lon"])
                node["pos"]["lat"] = float(element.attrib["lat"])
            except KeyError:
                pass
            node["_id"] = element.attrib["id"]
            node["type"] = element.tag
            if node["type"] == "node":
                node["created"] = {}
                children = element.findall("tag")
                for i in self.CREATED:
                    try:
                        print(i, element.attrib[i])
                        node["created"][i] = element.attrib[i]
                    except KeyError:
                        pass
            
            elif node["type"] == "way":
                node["node_refs"] = [child.attrib['ref'] for child in element.findall("nd")]
                children = element.iter()
            for k, v in element.attrib.items():
                
                if not k or k == "" or v == "" or v is None:         
                    self._rejects.add((k, v, node["type"]))

                elif k not in self.excluded:
                    node[k] = v
                    self._passed.add((k, v, node["type"]))
                
                else:
                    self._rejects.add((k, v, node["type"]))
            
            
            if children:
                node["address"] = {}
                for el_lst in children:
                    el_dict = el_lst.attrib
                    k = ""
                    v = ""
                    try:
                        k = el_dict['k']
                        v = el_dict['v']
                    except KeyError:
                        pass
   
                    if self.problemchars.search(k) or k == "" or v == "":
                        self._prob.add((k, v, node["type"]))
                
                    else:    
                        
                        #Filters unwanted values/sub-names such as address constituents
                        if self.filternames.search(k) and len(k.split(":")) <= 2:
                            #Removes unwanted strings such as 'addr:' or 'gris:'
                            ks = k.split(":")[-1]
                            k = self.align_name([ks])
                            v = re.sub('_', ' ', v)
                            v = v.split()
                            v = self.align_name(v)
                            if k.lower() in ns and not ''.join(v).isdigit():
                                #Capitalize all words in name/street element
                                v = v.title()
                                v = ' '.join([word.capitalize() for word in v.split() if word not in ["the", "of"]])
                                v = self.align_name([v])

                            if self.addrnames.search(k):
                                node["address"][k] = v
                            
                            else:
                                node[k] = v
                                
                            self._passed.add((k, v, node["type"]))
                            

                        else:
                    
                            self._rejects.add((k, v, node["type"]))
                            
                element.clear()
                
            for key, value in node.items():
                if value == {} or not value:
                    #delete blank/empty attributes
                    del node[key]       
              
            return node            
        else:
            return None   

    def process_map(self, file_in, pretty = True):
        
        file_out = "{0}.json".format(os.path.splitext(os.path.basename(file_in))[0])
        file_out_path = os.path.join(os.path.dirname(file_in), file_out)
        if os.path.isfile(file_out_path):
            os.remove(file_out_path)
        with codecs.open(file_out_path, "w") as fo:
            for event, element in ET.iterparse(file_in):
                
                el = self.shape_element(element)
                if el:
                    if pretty:
                        fo.write(json.dumps(el, indent=2)+"\n")
                    else:
                        fo.write(json.dumps(el) + "\n")

    @property
    def rejects(self):
        return self._rejects
    
    @property
    def passed(self):
        return self._passed
    
    @property    
    def prob(self):
        return self._prob

#x = Mapparser(filename)
#with open(r'rejects.txt', 'a') as rejected:
#    for i in x.rejects:
#        rejected.write(str(i))
#with open(r'probs.txt', 'a') as probs:
#    for i in x.prob:
#        probs.write(str(i))
    
def Mongo_import():
    client = MongoClient('mongodb://localhost:27017/')
    db = client.examples
    small_posts = db.small_posts
        
    with open(r'C:\Users\Toshiki_Nazikian\Downloads\SD_city.json') as data_file:
        for i in data_file.readlines():
            data = json.loads(i)
            try:    
                db.small_posts.insert_one(data) 
            except:
                del data["_id"]
                db.small_posts.insert_one(data)
                continue
                
        print(db.small_posts.count())



client = MongoClient('mongodb://localhost:27017/')
db = client.examples
#db.small_posts.remove({})
#Mongo_import()
pipeline = [
    {"$match": {"amenity":{"$exists":1}, "$and":[{"pos.lat":{"$gt":32.8134, "$lt":32.8383}}, {"pos.lon":{"$gt":-117.1693, "$lt":-117.1353}}]}},
    {"$group": {"_id": "$amenity", "count": {"$sum": 1}}},
    {"$sort": {"count":-1}},
    {"$limit":20}
]


convy = db.small_posts.aggregate(pipeline)
#print(convy.count())
for i in convy:
    print(i)
print("done")
#for item in db.posts.find():
#    db.posts.update_one({"_id": item["_id"]}, {"$set":{"num_fields":len(item)}})
#db.posts.update_many({"name":"Starbucks Coffee"}, 
#    {"$set": {"amenity":"cafe"}})
#query_docs = db.small_posts.aggregate(pipeline)
#for i in query_docs:
#    print("{0}: {1}".format(i['_id'], i['count']))

#for document in node_num:
#    print(document.attrib)




#for event, elem in ET.iterparse("C:\Users\Toshiki_Nazikian\Downloads\San-Diego_California.osm"):
#    if i < 50:
#        i += 1
#        print(elem.attrib, elem.tag)
#    else:
#        break
#posts = db.posts.find({"address.postcode":{"$exists":1}})
#codes = set()
#for i in posts:
#    codes.add(i["address"]["postcode"])
#print(codes)
  
#posts = db.posts.remove({"address.postcode":{"$exists":0}}, {"address.postcode": {"$regex": "^\d{5}(?:[-\s]\d{4})?$"}})
#db.posts.update({"address.postcode":{"$exists":1}}, {"$set": {"address.postcode":"address.postcode".split(' ')[-1]"}}, multi=True)
#for i in db.posts.find():
#    pprint.pprint(i)
            
#for k in namez:            
#    print(k)

#t = Timer('Mapparser(filename).rejects', "from __main__ import filename, Mapparser, mapping")
#print (t.timeit())


#pprint(data)
    
#if __name__ == "__main__":


#for i in x:
    #print(i)
#index = 0
#for i in x:
    #print(i)
    #index += 1
    # try:
    #    print(i.address)
    #except AttributeError:
    #    print("Element {0} has no address".format(index))
    

    #c = Mapparser("C:\Users\Toshiki_Nazikian\Downloads\chicago_illinois.osm")
    #data = c.datas
    #print(data)


# In[ ]:



