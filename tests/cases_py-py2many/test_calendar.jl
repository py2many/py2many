using PyCall
using Test
datetime = pyimport("datetime")
import calendar


using test.support.script_helper: assert_python_ok, assert_python_failure

import locale



abstract type AbstractOutputTestCase end
abstract type AbstractCalendarTestCase end
abstract type AbstractMonthCalendarTestCase end
abstract type AbstractMondayTestCase <: AbstractMonthCalendarTestCase end
abstract type AbstractSundayTestCase <: AbstractMonthCalendarTestCase end
abstract type AbstractTimegmTestCase end
abstract type AbstractMonthRangeTestCase end
abstract type AbstractLeapdaysTestCase end
abstract type AbstractCommandLineTestCase end
abstract type AbstractMiscTestCase end
abstract type AbstractTestSubClassingCase end
abstract type AbstractCustomHTMLCal <: Abstractcalendar.HTMLCalendar end
result_0_02_text = "     February 0\nMo Tu We Th Fr Sa Su\n    1  2  3  4  5  6\n 7  8  9 10 11 12 13\n14 15 16 17 18 19 20\n21 22 23 24 25 26 27\n28 29\n"
result_0_text = "                                   0\n\n      January                   February                   March\nMo Tu We Th Fr Sa Su      Mo Tu We Th Fr Sa Su      Mo Tu We Th Fr Sa Su\n                1  2          1  2  3  4  5  6             1  2  3  4  5\n 3  4  5  6  7  8  9       7  8  9 10 11 12 13       6  7  8  9 10 11 12\n10 11 12 13 14 15 16      14 15 16 17 18 19 20      13 14 15 16 17 18 19\n17 18 19 20 21 22 23      21 22 23 24 25 26 27      20 21 22 23 24 25 26\n24 25 26 27 28 29 30      28 29                     27 28 29 30 31\n31\n\n       April                      May                       June\nMo Tu We Th Fr Sa Su      Mo Tu We Th Fr Sa Su      Mo Tu We Th Fr Sa Su\n                1  2       1  2  3  4  5  6  7                1  2  3  4\n 3  4  5  6  7  8  9       8  9 10 11 12 13 14       5  6  7  8  9 10 11\n10 11 12 13 14 15 16      15 16 17 18 19 20 21      12 13 14 15 16 17 18\n17 18 19 20 21 22 23      22 23 24 25 26 27 28      19 20 21 22 23 24 25\n24 25 26 27 28 29 30      29 30 31                  26 27 28 29 30\n\n        July                     August                  September\nMo Tu We Th Fr Sa Su      Mo Tu We Th Fr Sa Su      Mo Tu We Th Fr Sa Su\n                1  2          1  2  3  4  5  6                   1  2  3\n 3  4  5  6  7  8  9       7  8  9 10 11 12 13       4  5  6  7  8  9 10\n10 11 12 13 14 15 16      14 15 16 17 18 19 20      11 12 13 14 15 16 17\n17 18 19 20 21 22 23      21 22 23 24 25 26 27      18 19 20 21 22 23 24\n24 25 26 27 28 29 30      28 29 30 31               25 26 27 28 29 30\n31\n\n      October                   November                  December\nMo Tu We Th Fr Sa Su      Mo Tu We Th Fr Sa Su      Mo Tu We Th Fr Sa Su\n                   1             1  2  3  4  5                   1  2  3\n 2  3  4  5  6  7  8       6  7  8  9 10 11 12       4  5  6  7  8  9 10\n 9 10 11 12 13 14 15      13 14 15 16 17 18 19      11 12 13 14 15 16 17\n16 17 18 19 20 21 22      20 21 22 23 24 25 26      18 19 20 21 22 23 24\n23 24 25 26 27 28 29      27 28 29 30               25 26 27 28 29 30 31\n30 31\n"
result_2004_01_text = "    January 2004\nMo Tu We Th Fr Sa Su\n          1  2  3  4\n 5  6  7  8  9 10 11\n12 13 14 15 16 17 18\n19 20 21 22 23 24 25\n26 27 28 29 30 31\n"
result_2004_text = "                                  2004\n\n      January                   February                   March\nMo Tu We Th Fr Sa Su      Mo Tu We Th Fr Sa Su      Mo Tu We Th Fr Sa Su\n          1  2  3  4                         1       1  2  3  4  5  6  7\n 5  6  7  8  9 10 11       2  3  4  5  6  7  8       8  9 10 11 12 13 14\n12 13 14 15 16 17 18       9 10 11 12 13 14 15      15 16 17 18 19 20 21\n19 20 21 22 23 24 25      16 17 18 19 20 21 22      22 23 24 25 26 27 28\n26 27 28 29 30 31         23 24 25 26 27 28 29      29 30 31\n\n       April                      May                       June\nMo Tu We Th Fr Sa Su      Mo Tu We Th Fr Sa Su      Mo Tu We Th Fr Sa Su\n          1  2  3  4                      1  2          1  2  3  4  5  6\n 5  6  7  8  9 10 11       3  4  5  6  7  8  9       7  8  9 10 11 12 13\n12 13 14 15 16 17 18      10 11 12 13 14 15 16      14 15 16 17 18 19 20\n19 20 21 22 23 24 25      17 18 19 20 21 22 23      21 22 23 24 25 26 27\n26 27 28 29 30            24 25 26 27 28 29 30      28 29 30\n                          31\n\n        July                     August                  September\nMo Tu We Th Fr Sa Su      Mo Tu We Th Fr Sa Su      Mo Tu We Th Fr Sa Su\n          1  2  3  4                         1             1  2  3  4  5\n 5  6  7  8  9 10 11       2  3  4  5  6  7  8       6  7  8  9 10 11 12\n12 13 14 15 16 17 18       9 10 11 12 13 14 15      13 14 15 16 17 18 19\n19 20 21 22 23 24 25      16 17 18 19 20 21 22      20 21 22 23 24 25 26\n26 27 28 29 30 31         23 24 25 26 27 28 29      27 28 29 30\n                          30 31\n\n      October                   November                  December\nMo Tu We Th Fr Sa Su      Mo Tu We Th Fr Sa Su      Mo Tu We Th Fr Sa Su\n             1  2  3       1  2  3  4  5  6  7             1  2  3  4  5\n 4  5  6  7  8  9 10       8  9 10 11 12 13 14       6  7  8  9 10 11 12\n11 12 13 14 15 16 17      15 16 17 18 19 20 21      13 14 15 16 17 18 19\n18 19 20 21 22 23 24      22 23 24 25 26 27 28      20 21 22 23 24 25 26\n25 26 27 28 29 30 31      29 30                     27 28 29 30 31\n"
default_format = dict("year", "month", "ascii")
result_2004_html = "<?xml version=\"1.0\" encoding=\"{encoding}\"?>\n<!DOCTYPE html PUBLIC \"-//W3C//DTD XHTML 1.0 Strict//EN\" \"http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd\">\n<html>\n<head>\n<meta http-equiv=\"Content-Type\" content=\"text/html; charset={encoding}\" />\n<link rel=\"stylesheet\" type=\"text/css\" href=\"calendar.css\" />\n<title>Calendar for 2004</title>\n</head>\n<body>\n<table border=\"0\" cellpadding=\"0\" cellspacing=\"0\" class=\"{year}\">\n<tr><th colspan=\"3\" class=\"{year}\">2004</th></tr><tr><td><table border=\"0\" cellpadding=\"0\" cellspacing=\"0\" class=\"{month}\">\n<tr><th colspan=\"7\" class=\"{month}\">January</th></tr>\n<tr><th class=\"mon\">Mon</th><th class=\"tue\">Tue</th><th class=\"wed\">Wed</th><th class=\"thu\">Thu</th><th class=\"fri\">Fri</th><th class=\"sat\">Sat</th><th class=\"sun\">Sun</th></tr>\n<tr><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td><td class=\"thu\">1</td><td class=\"fri\">2</td><td class=\"sat\">3</td><td class=\"sun\">4</td></tr>\n<tr><td class=\"mon\">5</td><td class=\"tue\">6</td><td class=\"wed\">7</td><td class=\"thu\">8</td><td class=\"fri\">9</td><td class=\"sat\">10</td><td class=\"sun\">11</td></tr>\n<tr><td class=\"mon\">12</td><td class=\"tue\">13</td><td class=\"wed\">14</td><td class=\"thu\">15</td><td class=\"fri\">16</td><td class=\"sat\">17</td><td class=\"sun\">18</td></tr>\n<tr><td class=\"mon\">19</td><td class=\"tue\">20</td><td class=\"wed\">21</td><td class=\"thu\">22</td><td class=\"fri\">23</td><td class=\"sat\">24</td><td class=\"sun\">25</td></tr>\n<tr><td class=\"mon\">26</td><td class=\"tue\">27</td><td class=\"wed\">28</td><td class=\"thu\">29</td><td class=\"fri\">30</td><td class=\"sat\">31</td><td class=\"noday\">&nbsp;</td></tr>\n</table>\n</td><td><table border=\"0\" cellpadding=\"0\" cellspacing=\"0\" class=\"{month}\">\n<tr><th colspan=\"7\" class=\"{month}\">February</th></tr>\n<tr><th class=\"mon\">Mon</th><th class=\"tue\">Tue</th><th class=\"wed\">Wed</th><th class=\"thu\">Thu</th><th class=\"fri\">Fri</th><th class=\"sat\">Sat</th><th class=\"sun\">Sun</th></tr>\n<tr><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td><td class=\"sun\">1</td></tr>\n<tr><td class=\"mon\">2</td><td class=\"tue\">3</td><td class=\"wed\">4</td><td class=\"thu\">5</td><td class=\"fri\">6</td><td class=\"sat\">7</td><td class=\"sun\">8</td></tr>\n<tr><td class=\"mon\">9</td><td class=\"tue\">10</td><td class=\"wed\">11</td><td class=\"thu\">12</td><td class=\"fri\">13</td><td class=\"sat\">14</td><td class=\"sun\">15</td></tr>\n<tr><td class=\"mon\">16</td><td class=\"tue\">17</td><td class=\"wed\">18</td><td class=\"thu\">19</td><td class=\"fri\">20</td><td class=\"sat\">21</td><td class=\"sun\">22</td></tr>\n<tr><td class=\"mon\">23</td><td class=\"tue\">24</td><td class=\"wed\">25</td><td class=\"thu\">26</td><td class=\"fri\">27</td><td class=\"sat\">28</td><td class=\"sun\">29</td></tr>\n</table>\n</td><td><table border=\"0\" cellpadding=\"0\" cellspacing=\"0\" class=\"{month}\">\n<tr><th colspan=\"7\" class=\"{month}\">March</th></tr>\n<tr><th class=\"mon\">Mon</th><th class=\"tue\">Tue</th><th class=\"wed\">Wed</th><th class=\"thu\">Thu</th><th class=\"fri\">Fri</th><th class=\"sat\">Sat</th><th class=\"sun\">Sun</th></tr>\n<tr><td class=\"mon\">1</td><td class=\"tue\">2</td><td class=\"wed\">3</td><td class=\"thu\">4</td><td class=\"fri\">5</td><td class=\"sat\">6</td><td class=\"sun\">7</td></tr>\n<tr><td class=\"mon\">8</td><td class=\"tue\">9</td><td class=\"wed\">10</td><td class=\"thu\">11</td><td class=\"fri\">12</td><td class=\"sat\">13</td><td class=\"sun\">14</td></tr>\n<tr><td class=\"mon\">15</td><td class=\"tue\">16</td><td class=\"wed\">17</td><td class=\"thu\">18</td><td class=\"fri\">19</td><td class=\"sat\">20</td><td class=\"sun\">21</td></tr>\n<tr><td class=\"mon\">22</td><td class=\"tue\">23</td><td class=\"wed\">24</td><td class=\"thu\">25</td><td class=\"fri\">26</td><td class=\"sat\">27</td><td class=\"sun\">28</td></tr>\n<tr><td class=\"mon\">29</td><td class=\"tue\">30</td><td class=\"wed\">31</td><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td></tr>\n</table>\n</td></tr><tr><td><table border=\"0\" cellpadding=\"0\" cellspacing=\"0\" class=\"{month}\">\n<tr><th colspan=\"7\" class=\"{month}\">April</th></tr>\n<tr><th class=\"mon\">Mon</th><th class=\"tue\">Tue</th><th class=\"wed\">Wed</th><th class=\"thu\">Thu</th><th class=\"fri\">Fri</th><th class=\"sat\">Sat</th><th class=\"sun\">Sun</th></tr>\n<tr><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td><td class=\"thu\">1</td><td class=\"fri\">2</td><td class=\"sat\">3</td><td class=\"sun\">4</td></tr>\n<tr><td class=\"mon\">5</td><td class=\"tue\">6</td><td class=\"wed\">7</td><td class=\"thu\">8</td><td class=\"fri\">9</td><td class=\"sat\">10</td><td class=\"sun\">11</td></tr>\n<tr><td class=\"mon\">12</td><td class=\"tue\">13</td><td class=\"wed\">14</td><td class=\"thu\">15</td><td class=\"fri\">16</td><td class=\"sat\">17</td><td class=\"sun\">18</td></tr>\n<tr><td class=\"mon\">19</td><td class=\"tue\">20</td><td class=\"wed\">21</td><td class=\"thu\">22</td><td class=\"fri\">23</td><td class=\"sat\">24</td><td class=\"sun\">25</td></tr>\n<tr><td class=\"mon\">26</td><td class=\"tue\">27</td><td class=\"wed\">28</td><td class=\"thu\">29</td><td class=\"fri\">30</td><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td></tr>\n</table>\n</td><td><table border=\"0\" cellpadding=\"0\" cellspacing=\"0\" class=\"{month}\">\n<tr><th colspan=\"7\" class=\"{month}\">May</th></tr>\n<tr><th class=\"mon\">Mon</th><th class=\"tue\">Tue</th><th class=\"wed\">Wed</th><th class=\"thu\">Thu</th><th class=\"fri\">Fri</th><th class=\"sat\">Sat</th><th class=\"sun\">Sun</th></tr>\n<tr><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td><td class=\"sat\">1</td><td class=\"sun\">2</td></tr>\n<tr><td class=\"mon\">3</td><td class=\"tue\">4</td><td class=\"wed\">5</td><td class=\"thu\">6</td><td class=\"fri\">7</td><td class=\"sat\">8</td><td class=\"sun\">9</td></tr>\n<tr><td class=\"mon\">10</td><td class=\"tue\">11</td><td class=\"wed\">12</td><td class=\"thu\">13</td><td class=\"fri\">14</td><td class=\"sat\">15</td><td class=\"sun\">16</td></tr>\n<tr><td class=\"mon\">17</td><td class=\"tue\">18</td><td class=\"wed\">19</td><td class=\"thu\">20</td><td class=\"fri\">21</td><td class=\"sat\">22</td><td class=\"sun\">23</td></tr>\n<tr><td class=\"mon\">24</td><td class=\"tue\">25</td><td class=\"wed\">26</td><td class=\"thu\">27</td><td class=\"fri\">28</td><td class=\"sat\">29</td><td class=\"sun\">30</td></tr>\n<tr><td class=\"mon\">31</td><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td></tr>\n</table>\n</td><td><table border=\"0\" cellpadding=\"0\" cellspacing=\"0\" class=\"{month}\">\n<tr><th colspan=\"7\" class=\"{month}\">June</th></tr>\n<tr><th class=\"mon\">Mon</th><th class=\"tue\">Tue</th><th class=\"wed\">Wed</th><th class=\"thu\">Thu</th><th class=\"fri\">Fri</th><th class=\"sat\">Sat</th><th class=\"sun\">Sun</th></tr>\n<tr><td class=\"noday\">&nbsp;</td><td class=\"tue\">1</td><td class=\"wed\">2</td><td class=\"thu\">3</td><td class=\"fri\">4</td><td class=\"sat\">5</td><td class=\"sun\">6</td></tr>\n<tr><td class=\"mon\">7</td><td class=\"tue\">8</td><td class=\"wed\">9</td><td class=\"thu\">10</td><td class=\"fri\">11</td><td class=\"sat\">12</td><td class=\"sun\">13</td></tr>\n<tr><td class=\"mon\">14</td><td class=\"tue\">15</td><td class=\"wed\">16</td><td class=\"thu\">17</td><td class=\"fri\">18</td><td class=\"sat\">19</td><td class=\"sun\">20</td></tr>\n<tr><td class=\"mon\">21</td><td class=\"tue\">22</td><td class=\"wed\">23</td><td class=\"thu\">24</td><td class=\"fri\">25</td><td class=\"sat\">26</td><td class=\"sun\">27</td></tr>\n<tr><td class=\"mon\">28</td><td class=\"tue\">29</td><td class=\"wed\">30</td><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td></tr>\n</table>\n</td></tr><tr><td><table border=\"0\" cellpadding=\"0\" cellspacing=\"0\" class=\"{month}\">\n<tr><th colspan=\"7\" class=\"{month}\">July</th></tr>\n<tr><th class=\"mon\">Mon</th><th class=\"tue\">Tue</th><th class=\"wed\">Wed</th><th class=\"thu\">Thu</th><th class=\"fri\">Fri</th><th class=\"sat\">Sat</th><th class=\"sun\">Sun</th></tr>\n<tr><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td><td class=\"thu\">1</td><td class=\"fri\">2</td><td class=\"sat\">3</td><td class=\"sun\">4</td></tr>\n<tr><td class=\"mon\">5</td><td class=\"tue\">6</td><td class=\"wed\">7</td><td class=\"thu\">8</td><td class=\"fri\">9</td><td class=\"sat\">10</td><td class=\"sun\">11</td></tr>\n<tr><td class=\"mon\">12</td><td class=\"tue\">13</td><td class=\"wed\">14</td><td class=\"thu\">15</td><td class=\"fri\">16</td><td class=\"sat\">17</td><td class=\"sun\">18</td></tr>\n<tr><td class=\"mon\">19</td><td class=\"tue\">20</td><td class=\"wed\">21</td><td class=\"thu\">22</td><td class=\"fri\">23</td><td class=\"sat\">24</td><td class=\"sun\">25</td></tr>\n<tr><td class=\"mon\">26</td><td class=\"tue\">27</td><td class=\"wed\">28</td><td class=\"thu\">29</td><td class=\"fri\">30</td><td class=\"sat\">31</td><td class=\"noday\">&nbsp;</td></tr>\n</table>\n</td><td><table border=\"0\" cellpadding=\"0\" cellspacing=\"0\" class=\"{month}\">\n<tr><th colspan=\"7\" class=\"{month}\">August</th></tr>\n<tr><th class=\"mon\">Mon</th><th class=\"tue\">Tue</th><th class=\"wed\">Wed</th><th class=\"thu\">Thu</th><th class=\"fri\">Fri</th><th class=\"sat\">Sat</th><th class=\"sun\">Sun</th></tr>\n<tr><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td><td class=\"sun\">1</td></tr>\n<tr><td class=\"mon\">2</td><td class=\"tue\">3</td><td class=\"wed\">4</td><td class=\"thu\">5</td><td class=\"fri\">6</td><td class=\"sat\">7</td><td class=\"sun\">8</td></tr>\n<tr><td class=\"mon\">9</td><td class=\"tue\">10</td><td class=\"wed\">11</td><td class=\"thu\">12</td><td class=\"fri\">13</td><td class=\"sat\">14</td><td class=\"sun\">15</td></tr>\n<tr><td class=\"mon\">16</td><td class=\"tue\">17</td><td class=\"wed\">18</td><td class=\"thu\">19</td><td class=\"fri\">20</td><td class=\"sat\">21</td><td class=\"sun\">22</td></tr>\n<tr><td class=\"mon\">23</td><td class=\"tue\">24</td><td class=\"wed\">25</td><td class=\"thu\">26</td><td class=\"fri\">27</td><td class=\"sat\">28</td><td class=\"sun\">29</td></tr>\n<tr><td class=\"mon\">30</td><td class=\"tue\">31</td><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td></tr>\n</table>\n</td><td><table border=\"0\" cellpadding=\"0\" cellspacing=\"0\" class=\"{month}\">\n<tr><th colspan=\"7\" class=\"{month}\">September</th></tr>\n<tr><th class=\"mon\">Mon</th><th class=\"tue\">Tue</th><th class=\"wed\">Wed</th><th class=\"thu\">Thu</th><th class=\"fri\">Fri</th><th class=\"sat\">Sat</th><th class=\"sun\">Sun</th></tr>\n<tr><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td><td class=\"wed\">1</td><td class=\"thu\">2</td><td class=\"fri\">3</td><td class=\"sat\">4</td><td class=\"sun\">5</td></tr>\n<tr><td class=\"mon\">6</td><td class=\"tue\">7</td><td class=\"wed\">8</td><td class=\"thu\">9</td><td class=\"fri\">10</td><td class=\"sat\">11</td><td class=\"sun\">12</td></tr>\n<tr><td class=\"mon\">13</td><td class=\"tue\">14</td><td class=\"wed\">15</td><td class=\"thu\">16</td><td class=\"fri\">17</td><td class=\"sat\">18</td><td class=\"sun\">19</td></tr>\n<tr><td class=\"mon\">20</td><td class=\"tue\">21</td><td class=\"wed\">22</td><td class=\"thu\">23</td><td class=\"fri\">24</td><td class=\"sat\">25</td><td class=\"sun\">26</td></tr>\n<tr><td class=\"mon\">27</td><td class=\"tue\">28</td><td class=\"wed\">29</td><td class=\"thu\">30</td><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td></tr>\n</table>\n</td></tr><tr><td><table border=\"0\" cellpadding=\"0\" cellspacing=\"0\" class=\"{month}\">\n<tr><th colspan=\"7\" class=\"{month}\">October</th></tr>\n<tr><th class=\"mon\">Mon</th><th class=\"tue\">Tue</th><th class=\"wed\">Wed</th><th class=\"thu\">Thu</th><th class=\"fri\">Fri</th><th class=\"sat\">Sat</th><th class=\"sun\">Sun</th></tr>\n<tr><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td><td class=\"fri\">1</td><td class=\"sat\">2</td><td class=\"sun\">3</td></tr>\n<tr><td class=\"mon\">4</td><td class=\"tue\">5</td><td class=\"wed\">6</td><td class=\"thu\">7</td><td class=\"fri\">8</td><td class=\"sat\">9</td><td class=\"sun\">10</td></tr>\n<tr><td class=\"mon\">11</td><td class=\"tue\">12</td><td class=\"wed\">13</td><td class=\"thu\">14</td><td class=\"fri\">15</td><td class=\"sat\">16</td><td class=\"sun\">17</td></tr>\n<tr><td class=\"mon\">18</td><td class=\"tue\">19</td><td class=\"wed\">20</td><td class=\"thu\">21</td><td class=\"fri\">22</td><td class=\"sat\">23</td><td class=\"sun\">24</td></tr>\n<tr><td class=\"mon\">25</td><td class=\"tue\">26</td><td class=\"wed\">27</td><td class=\"thu\">28</td><td class=\"fri\">29</td><td class=\"sat\">30</td><td class=\"sun\">31</td></tr>\n</table>\n</td><td><table border=\"0\" cellpadding=\"0\" cellspacing=\"0\" class=\"{month}\">\n<tr><th colspan=\"7\" class=\"{month}\">November</th></tr>\n<tr><th class=\"mon\">Mon</th><th class=\"tue\">Tue</th><th class=\"wed\">Wed</th><th class=\"thu\">Thu</th><th class=\"fri\">Fri</th><th class=\"sat\">Sat</th><th class=\"sun\">Sun</th></tr>\n<tr><td class=\"mon\">1</td><td class=\"tue\">2</td><td class=\"wed\">3</td><td class=\"thu\">4</td><td class=\"fri\">5</td><td class=\"sat\">6</td><td class=\"sun\">7</td></tr>\n<tr><td class=\"mon\">8</td><td class=\"tue\">9</td><td class=\"wed\">10</td><td class=\"thu\">11</td><td class=\"fri\">12</td><td class=\"sat\">13</td><td class=\"sun\">14</td></tr>\n<tr><td class=\"mon\">15</td><td class=\"tue\">16</td><td class=\"wed\">17</td><td class=\"thu\">18</td><td class=\"fri\">19</td><td class=\"sat\">20</td><td class=\"sun\">21</td></tr>\n<tr><td class=\"mon\">22</td><td class=\"tue\">23</td><td class=\"wed\">24</td><td class=\"thu\">25</td><td class=\"fri\">26</td><td class=\"sat\">27</td><td class=\"sun\">28</td></tr>\n<tr><td class=\"mon\">29</td><td class=\"tue\">30</td><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td></tr>\n</table>\n</td><td><table border=\"0\" cellpadding=\"0\" cellspacing=\"0\" class=\"{month}\">\n<tr><th colspan=\"7\" class=\"{month}\">December</th></tr>\n<tr><th class=\"mon\">Mon</th><th class=\"tue\">Tue</th><th class=\"wed\">Wed</th><th class=\"thu\">Thu</th><th class=\"fri\">Fri</th><th class=\"sat\">Sat</th><th class=\"sun\">Sun</th></tr>\n<tr><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td><td class=\"wed\">1</td><td class=\"thu\">2</td><td class=\"fri\">3</td><td class=\"sat\">4</td><td class=\"sun\">5</td></tr>\n<tr><td class=\"mon\">6</td><td class=\"tue\">7</td><td class=\"wed\">8</td><td class=\"thu\">9</td><td class=\"fri\">10</td><td class=\"sat\">11</td><td class=\"sun\">12</td></tr>\n<tr><td class=\"mon\">13</td><td class=\"tue\">14</td><td class=\"wed\">15</td><td class=\"thu\">16</td><td class=\"fri\">17</td><td class=\"sat\">18</td><td class=\"sun\">19</td></tr>\n<tr><td class=\"mon\">20</td><td class=\"tue\">21</td><td class=\"wed\">22</td><td class=\"thu\">23</td><td class=\"fri\">24</td><td class=\"sat\">25</td><td class=\"sun\">26</td></tr>\n<tr><td class=\"mon\">27</td><td class=\"tue\">28</td><td class=\"wed\">29</td><td class=\"thu\">30</td><td class=\"fri\">31</td><td class=\"noday\">&nbsp;</td><td class=\"noday\">&nbsp;</td></tr>\n</table>\n</td></tr></table></body>\n</html>\n"
result_2004_days = [[[[0, 0, 0, 1, 2, 3, 4], [5, 6, 7, 8, 9, 10, 11], [12, 13, 14, 15, 16, 17, 18], [19, 20, 21, 22, 23, 24, 25], [26, 27, 28, 29, 30, 31, 0]], [[0, 0, 0, 0, 0, 0, 1], [2, 3, 4, 5, 6, 7, 8], [9, 10, 11, 12, 13, 14, 15], [16, 17, 18, 19, 20, 21, 22], [23, 24, 25, 26, 27, 28, 29]], [[1, 2, 3, 4, 5, 6, 7], [8, 9, 10, 11, 12, 13, 14], [15, 16, 17, 18, 19, 20, 21], [22, 23, 24, 25, 26, 27, 28], [29, 30, 31, 0, 0, 0, 0]]], [[[0, 0, 0, 1, 2, 3, 4], [5, 6, 7, 8, 9, 10, 11], [12, 13, 14, 15, 16, 17, 18], [19, 20, 21, 22, 23, 24, 25], [26, 27, 28, 29, 30, 0, 0]], [[0, 0, 0, 0, 0, 1, 2], [3, 4, 5, 6, 7, 8, 9], [10, 11, 12, 13, 14, 15, 16], [17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30], [31, 0, 0, 0, 0, 0, 0]], [[0, 1, 2, 3, 4, 5, 6], [7, 8, 9, 10, 11, 12, 13], [14, 15, 16, 17, 18, 19, 20], [21, 22, 23, 24, 25, 26, 27], [28, 29, 30, 0, 0, 0, 0]]], [[[0, 0, 0, 1, 2, 3, 4], [5, 6, 7, 8, 9, 10, 11], [12, 13, 14, 15, 16, 17, 18], [19, 20, 21, 22, 23, 24, 25], [26, 27, 28, 29, 30, 31, 0]], [[0, 0, 0, 0, 0, 0, 1], [2, 3, 4, 5, 6, 7, 8], [9, 10, 11, 12, 13, 14, 15], [16, 17, 18, 19, 20, 21, 22], [23, 24, 25, 26, 27, 28, 29], [30, 31, 0, 0, 0, 0, 0]], [[0, 0, 1, 2, 3, 4, 5], [6, 7, 8, 9, 10, 11, 12], [13, 14, 15, 16, 17, 18, 19], [20, 21, 22, 23, 24, 25, 26], [27, 28, 29, 30, 0, 0, 0]]], [[[0, 0, 0, 0, 1, 2, 3], [4, 5, 6, 7, 8, 9, 10], [11, 12, 13, 14, 15, 16, 17], [18, 19, 20, 21, 22, 23, 24], [25, 26, 27, 28, 29, 30, 31]], [[1, 2, 3, 4, 5, 6, 7], [8, 9, 10, 11, 12, 13, 14], [15, 16, 17, 18, 19, 20, 21], [22, 23, 24, 25, 26, 27, 28], [29, 30, 0, 0, 0, 0, 0]], [[0, 0, 1, 2, 3, 4, 5], [6, 7, 8, 9, 10, 11, 12], [13, 14, 15, 16, 17, 18, 19], [20, 21, 22, 23, 24, 25, 26], [27, 28, 29, 30, 31, 0, 0]]]]
result_2004_dates = [[["12/29/03 12/30/03 12/31/03 01/01/04 01/02/04 01/03/04 01/04/04", "01/05/04 01/06/04 01/07/04 01/08/04 01/09/04 01/10/04 01/11/04", "01/12/04 01/13/04 01/14/04 01/15/04 01/16/04 01/17/04 01/18/04", "01/19/04 01/20/04 01/21/04 01/22/04 01/23/04 01/24/04 01/25/04", "01/26/04 01/27/04 01/28/04 01/29/04 01/30/04 01/31/04 02/01/04"], ["01/26/04 01/27/04 01/28/04 01/29/04 01/30/04 01/31/04 02/01/04", "02/02/04 02/03/04 02/04/04 02/05/04 02/06/04 02/07/04 02/08/04", "02/09/04 02/10/04 02/11/04 02/12/04 02/13/04 02/14/04 02/15/04", "02/16/04 02/17/04 02/18/04 02/19/04 02/20/04 02/21/04 02/22/04", "02/23/04 02/24/04 02/25/04 02/26/04 02/27/04 02/28/04 02/29/04"], ["03/01/04 03/02/04 03/03/04 03/04/04 03/05/04 03/06/04 03/07/04", "03/08/04 03/09/04 03/10/04 03/11/04 03/12/04 03/13/04 03/14/04", "03/15/04 03/16/04 03/17/04 03/18/04 03/19/04 03/20/04 03/21/04", "03/22/04 03/23/04 03/24/04 03/25/04 03/26/04 03/27/04 03/28/04", "03/29/04 03/30/04 03/31/04 04/01/04 04/02/04 04/03/04 04/04/04"]], [["03/29/04 03/30/04 03/31/04 04/01/04 04/02/04 04/03/04 04/04/04", "04/05/04 04/06/04 04/07/04 04/08/04 04/09/04 04/10/04 04/11/04", "04/12/04 04/13/04 04/14/04 04/15/04 04/16/04 04/17/04 04/18/04", "04/19/04 04/20/04 04/21/04 04/22/04 04/23/04 04/24/04 04/25/04", "04/26/04 04/27/04 04/28/04 04/29/04 04/30/04 05/01/04 05/02/04"], ["04/26/04 04/27/04 04/28/04 04/29/04 04/30/04 05/01/04 05/02/04", "05/03/04 05/04/04 05/05/04 05/06/04 05/07/04 05/08/04 05/09/04", "05/10/04 05/11/04 05/12/04 05/13/04 05/14/04 05/15/04 05/16/04", "05/17/04 05/18/04 05/19/04 05/20/04 05/21/04 05/22/04 05/23/04", "05/24/04 05/25/04 05/26/04 05/27/04 05/28/04 05/29/04 05/30/04", "05/31/04 06/01/04 06/02/04 06/03/04 06/04/04 06/05/04 06/06/04"], ["05/31/04 06/01/04 06/02/04 06/03/04 06/04/04 06/05/04 06/06/04", "06/07/04 06/08/04 06/09/04 06/10/04 06/11/04 06/12/04 06/13/04", "06/14/04 06/15/04 06/16/04 06/17/04 06/18/04 06/19/04 06/20/04", "06/21/04 06/22/04 06/23/04 06/24/04 06/25/04 06/26/04 06/27/04", "06/28/04 06/29/04 06/30/04 07/01/04 07/02/04 07/03/04 07/04/04"]], [["06/28/04 06/29/04 06/30/04 07/01/04 07/02/04 07/03/04 07/04/04", "07/05/04 07/06/04 07/07/04 07/08/04 07/09/04 07/10/04 07/11/04", "07/12/04 07/13/04 07/14/04 07/15/04 07/16/04 07/17/04 07/18/04", "07/19/04 07/20/04 07/21/04 07/22/04 07/23/04 07/24/04 07/25/04", "07/26/04 07/27/04 07/28/04 07/29/04 07/30/04 07/31/04 08/01/04"], ["07/26/04 07/27/04 07/28/04 07/29/04 07/30/04 07/31/04 08/01/04", "08/02/04 08/03/04 08/04/04 08/05/04 08/06/04 08/07/04 08/08/04", "08/09/04 08/10/04 08/11/04 08/12/04 08/13/04 08/14/04 08/15/04", "08/16/04 08/17/04 08/18/04 08/19/04 08/20/04 08/21/04 08/22/04", "08/23/04 08/24/04 08/25/04 08/26/04 08/27/04 08/28/04 08/29/04", "08/30/04 08/31/04 09/01/04 09/02/04 09/03/04 09/04/04 09/05/04"], ["08/30/04 08/31/04 09/01/04 09/02/04 09/03/04 09/04/04 09/05/04", "09/06/04 09/07/04 09/08/04 09/09/04 09/10/04 09/11/04 09/12/04", "09/13/04 09/14/04 09/15/04 09/16/04 09/17/04 09/18/04 09/19/04", "09/20/04 09/21/04 09/22/04 09/23/04 09/24/04 09/25/04 09/26/04", "09/27/04 09/28/04 09/29/04 09/30/04 10/01/04 10/02/04 10/03/04"]], [["09/27/04 09/28/04 09/29/04 09/30/04 10/01/04 10/02/04 10/03/04", "10/04/04 10/05/04 10/06/04 10/07/04 10/08/04 10/09/04 10/10/04", "10/11/04 10/12/04 10/13/04 10/14/04 10/15/04 10/16/04 10/17/04", "10/18/04 10/19/04 10/20/04 10/21/04 10/22/04 10/23/04 10/24/04", "10/25/04 10/26/04 10/27/04 10/28/04 10/29/04 10/30/04 10/31/04"], ["11/01/04 11/02/04 11/03/04 11/04/04 11/05/04 11/06/04 11/07/04", "11/08/04 11/09/04 11/10/04 11/11/04 11/12/04 11/13/04 11/14/04", "11/15/04 11/16/04 11/17/04 11/18/04 11/19/04 11/20/04 11/21/04", "11/22/04 11/23/04 11/24/04 11/25/04 11/26/04 11/27/04 11/28/04", "11/29/04 11/30/04 12/01/04 12/02/04 12/03/04 12/04/04 12/05/04"], ["11/29/04 11/30/04 12/01/04 12/02/04 12/03/04 12/04/04 12/05/04", "12/06/04 12/07/04 12/08/04 12/09/04 12/10/04 12/11/04 12/12/04", "12/13/04 12/14/04 12/15/04 12/16/04 12/17/04 12/18/04 12/19/04", "12/20/04 12/21/04 12/22/04 12/23/04 12/24/04 12/25/04 12/26/04", "12/27/04 12/28/04 12/29/04 12/30/04 12/31/04 01/01/05 01/02/05"]]]
mutable struct OutputTestCase <: AbstractOutputTestCase

end
function normalize_calendar(self::OutputTestCase, s)::Vector
function neitherspacenordigit(c)
return !isspace(c) && !isdigit(c)
end

lines = []
for line in splitlines(s, false)
if line && !filter(neitherspacenordigit, line)
push!(lines, line)
end
end
return lines
end

function check_htmlcalendar_encoding(self::OutputTestCase, req, res)
cal = HTMLCalendar(calendar)
format_ = copy(default_format)
format_["encoding"] = req || "utf-8"
output = formatyearpage(cal, 2004, req)
@test (output == Vector{UInt8}(result_2004_html))
end

function test_output(self::OutputTestCase)
@test (normalize_calendar(self, calendar(calendar, 2004)) == normalize_calendar(self, result_2004_text))
@test (normalize_calendar(self, calendar(calendar, 0)) == normalize_calendar(self, result_0_text))
end

function test_output_textcalendar(self::OutputTestCase)
@test (formatyear(TextCalendar(calendar), 2004) == result_2004_text)
@test (formatyear(TextCalendar(calendar), 0) == result_0_text)
end

function test_output_htmlcalendar_encoding_ascii(self::OutputTestCase)
check_htmlcalendar_encoding(self, "ascii", "ascii")
end

function test_output_htmlcalendar_encoding_utf8(self::OutputTestCase)
check_htmlcalendar_encoding(self, "utf-8", "utf-8")
end

function test_output_htmlcalendar_encoding_default(self::OutputTestCase)
check_htmlcalendar_encoding(self, nothing, getdefaultencoding(sys))
end

function test_yeardatescalendar(self::OutputTestCase)
function shrink(cal)
return [[[join(("$(:d.month2d)/$(:02d)/$()" for d in z), " ") for z in y] for y in x] for x in cal]
end

@test (shrink(yeardatescalendar(Calendar(calendar), 2004)) == result_2004_dates)
end

function test_yeardayscalendar(self::OutputTestCase)
@test (yeardayscalendar(Calendar(calendar), 2004) == result_2004_days)
end

function test_formatweekheader_short(self::OutputTestCase)
@test (formatweekheader(TextCalendar(calendar), 2) == "Mo Tu We Th Fr Sa Su")
end

function test_formatweekheader_long(self::OutputTestCase)
@test (formatweekheader(TextCalendar(calendar), 9) == "  Monday   Tuesday  Wednesday  Thursday   Friday   Saturday   Sunday ")
end

function test_formatmonth(self::OutputTestCase)
@test (formatmonth(TextCalendar(calendar), 2004, 1) == result_2004_01_text)
@test (formatmonth(TextCalendar(calendar), 0, 2) == result_0_02_text)
end

function test_formatmonthname_with_year(self::OutputTestCase)
@test (formatmonthname(HTMLCalendar(calendar), 2004, 1, true) == "<tr><th colspan=\"7\" class=\"month\">January 2004</th></tr>")
end

function test_formatmonthname_without_year(self::OutputTestCase)
@test (formatmonthname(HTMLCalendar(calendar), 2004, 1, false) == "<tr><th colspan=\"7\" class=\"month\">January</th></tr>")
end

function test_prweek(self::OutputTestCase)
captured_stdout(support) do out 
week = [(1, 0), (2, 1), (3, 2), (4, 3), (5, 4), (6, 5), (7, 6)]
prweek(TextCalendar(calendar), week, 1)
@test (getvalue(out) == " 1  2  3  4  5  6  7")
end
end

function test_prmonth(self::OutputTestCase)
captured_stdout(support) do out 
prmonth(TextCalendar(calendar), 2004, 1)
@test (getvalue(out) == result_2004_01_text)
end
end

function test_pryear(self::OutputTestCase)
captured_stdout(support) do out 
pryear(TextCalendar(calendar), 2004)
@test (getvalue(out) == result_2004_text)
end
end

function test_format(self::OutputTestCase)
captured_stdout(support) do out 
calendar
@test (strip(getvalue(out)) == "1   2   3")
end
end

mutable struct CalendarTestCase <: AbstractCalendarTestCase

end
function test_isleap(self::CalendarTestCase)
@test (isleap(calendar, 2000) == 1)
@test (isleap(calendar, 2001) == 0)
@test (isleap(calendar, 2002) == 0)
@test (isleap(calendar, 2003) == 0)
end

function test_setfirstweekday(self::CalendarTestCase)
@test_throws TypeError calendar.setfirstweekday("flabber")
@test_throws ValueError calendar.setfirstweekday(-1)
@test_throws ValueError calendar.setfirstweekday(200)
orig = firstweekday(calendar)
setfirstweekday(calendar, calendar.SUNDAY)
@test (firstweekday(calendar) == calendar.SUNDAY)
setfirstweekday(calendar, calendar.MONDAY)
@test (firstweekday(calendar) == calendar.MONDAY)
setfirstweekday(calendar, orig)
end

function test_illegal_weekday_reported(self::CalendarTestCase)
assertRaisesRegex(self, calendar.IllegalWeekdayError, "123") do 
setfirstweekday(calendar, 123)
end
end

function test_enumerate_weekdays(self::CalendarTestCase)
@test_throws IndexError calendar.day_abbr.__getitem__(-10)
@test_throws IndexError calendar.day_name.__getitem__(10)
@test (length([d for d in calendar.day_abbr]) == 7)
end

function test_days(self::CalendarTestCase)
for attr in ("day_name", "day_abbr")
value = getfield(calendar, attr
@test (length(value) == 7)
@test (length(value[begin:end]) == 7)
@test (length(set(value)) == 7)
@test (value[end:-1:begin] == collect(reversed(value)))
end
end

function test_months(self::CalendarTestCase)
for attr in ("month_name", "month_abbr")
value = getfield(calendar, attr
@test (length(value) == 13)
@test (length(value[begin:end]) == 13)
@test (value[1] == "")
@test (length(set(value)) == 13)
@test (value[end:-1:begin] == collect(reversed(value)))
end
end

function test_locale_calendars(self::CalendarTestCase)
old_october = formatmonthname(TextCalendar(calendar), 2010, 10, 10)
try
cal = LocaleTextCalendar(calendar, "")
local_weekday = formatweekday(cal, 1, 10)
local_month = formatmonthname(cal, 2010, 10, 10)
catch exn
if exn isa locale.Error
throw(SkipTest(unittest, "cannot set the system default locale"))
end
end
@test isa(self, local_weekday)
@test isa(self, local_month)
@test (length(local_weekday) == 10)
assertGreaterEqual(self, length(local_month), 10)
cal = LocaleHTMLCalendar(calendar, "")
local_weekday = formatweekday(cal, 1)
local_month = formatmonthname(cal, 2010, 10)
@test isa(self, local_weekday)
@test isa(self, local_month)
new_october = formatmonthname(TextCalendar(calendar), 2010, 10, 10)
@test (old_october == new_october)
end

function test_locale_html_calendar_custom_css_class_month_name(self::CalendarTestCase)
try
cal = LocaleHTMLCalendar(calendar, "")
local_month = formatmonthname(cal, 2010, 10, 10)
catch exn
if exn isa locale.Error
throw(SkipTest(unittest, "cannot set the system default locale"))
end
end
assertIn(self, "class=\"month\"", local_month)
cal.cssclass_month_head = "text-center month"
local_month = formatmonthname(cal, 2010, 10, 10)
assertIn(self, "class=\"text-center month\"", local_month)
end

function test_locale_html_calendar_custom_css_class_weekday(self::CalendarTestCase)
try
cal = LocaleHTMLCalendar(calendar, "")
local_weekday = formatweekday(cal, 6)
catch exn
if exn isa locale.Error
throw(SkipTest(unittest, "cannot set the system default locale"))
end
end
assertIn(self, "class=\"sun\"", local_weekday)
cal.cssclasses_weekday_head = ["mon2", "tue2", "wed2", "thu2", "fri2", "sat2", "sun2"]
local_weekday = formatweekday(cal, 6)
assertIn(self, "class=\"sun2\"", local_weekday)
end

function test_itermonthdays3(self::CalendarTestCase)
collect(itermonthdays3(Calendar(calendar), datetime.MAXYEAR, 12))
end

function test_itermonthdays4(self::CalendarTestCase)
cal = Calendar(calendar, 3)
days = collect(itermonthdays4(cal, 2001, 2))
@test (days[1] == (2001, 2, 1, 3))
@test (days[end] == (2001, 2, 28, 2))
end

function test_itermonthdays(self::CalendarTestCase)
for firstweekday in 0:6
cal = Calendar(calendar, firstweekday)
for (y, m) in [(1, 1), (9999, 12)]
days = collect(itermonthdays(cal, y, m))
assertIn(self, length(days), (35, 42))
end
end
cal = Calendar(calendar, 3)
days = collect(itermonthdays(cal, 2001, 2))
@test (days == collect(1:28))
end

function test_itermonthdays2(self::CalendarTestCase)
for firstweekday in 0:6
cal = Calendar(calendar, firstweekday)
for (y, m) in [(1, 1), (9999, 12)]
days = collect(itermonthdays2(cal, y, m))
@test (days[1][2] == firstweekday)
@test (days[end][2] == (firstweekday - 1) % 7)
end
end
end

mutable struct MonthCalendarTestCase <: AbstractMonthCalendarTestCase
oldfirstweekday
firstweekday
end
function setUp(self::MonthCalendarTestCase)
self.oldfirstweekday = firstweekday(calendar)
setfirstweekday(calendar, self.firstweekday)
end

function tearDown(self::MonthCalendarTestCase)
setfirstweekday(calendar, self.oldfirstweekday)
end

function check_weeks(self::MonthCalendarTestCase, year, month, weeks)
cal = monthcalendar(calendar, year, month)
@test (length(cal) == length(weeks))
for i in 0:length(weeks) - 1
@test (weeks[i + 1] == sum((day != 0 for day in cal[i + 1])))
end
end

mutable struct MondayTestCase <: AbstractMondayTestCase
firstweekday

                    MondayTestCase(firstweekday = calendar.MONDAY) =
                        new(firstweekday)
end
function test_february(self::MondayTestCase)
check_weeks(self, 1999, 2, (7, 7, 7, 7))
check_weeks(self, 2005, 2, (6, 7, 7, 7, 1))
check_weeks(self, 1987, 2, (1, 7, 7, 7, 6))
check_weeks(self, 1988, 2, (7, 7, 7, 7, 1))
check_weeks(self, 1972, 2, (6, 7, 7, 7, 2))
check_weeks(self, 2004, 2, (1, 7, 7, 7, 7))
end

function test_april(self::MondayTestCase)
check_weeks(self, 1935, 4, (7, 7, 7, 7, 2))
check_weeks(self, 1975, 4, (6, 7, 7, 7, 3))
check_weeks(self, 1945, 4, (1, 7, 7, 7, 7, 1))
check_weeks(self, 1995, 4, (2, 7, 7, 7, 7))
check_weeks(self, 1994, 4, (3, 7, 7, 7, 6))
end

function test_december(self::MondayTestCase)
check_weeks(self, 1980, 12, (7, 7, 7, 7, 3))
check_weeks(self, 1987, 12, (6, 7, 7, 7, 4))
check_weeks(self, 1968, 12, (1, 7, 7, 7, 7, 2))
check_weeks(self, 1988, 12, (4, 7, 7, 7, 6))
check_weeks(self, 2017, 12, (3, 7, 7, 7, 7))
check_weeks(self, 2068, 12, (2, 7, 7, 7, 7, 1))
end

mutable struct SundayTestCase <: AbstractSundayTestCase
firstweekday

                    SundayTestCase(firstweekday = calendar.SUNDAY) =
                        new(firstweekday)
end
function test_february(self::SundayTestCase)
check_weeks(self, 2009, 2, (7, 7, 7, 7))
check_weeks(self, 1999, 2, (6, 7, 7, 7, 1))
check_weeks(self, 1997, 2, (1, 7, 7, 7, 6))
check_weeks(self, 2004, 2, (7, 7, 7, 7, 1))
check_weeks(self, 1960, 2, (6, 7, 7, 7, 2))
check_weeks(self, 1964, 2, (1, 7, 7, 7, 7))
end

function test_april(self::SundayTestCase)
check_weeks(self, 1923, 4, (7, 7, 7, 7, 2))
check_weeks(self, 1918, 4, (6, 7, 7, 7, 3))
check_weeks(self, 1950, 4, (1, 7, 7, 7, 7, 1))
check_weeks(self, 1960, 4, (2, 7, 7, 7, 7))
check_weeks(self, 1909, 4, (3, 7, 7, 7, 6))
end

function test_december(self::SundayTestCase)
check_weeks(self, 2080, 12, (7, 7, 7, 7, 3))
check_weeks(self, 1941, 12, (6, 7, 7, 7, 4))
check_weeks(self, 1923, 12, (1, 7, 7, 7, 7, 2))
check_weeks(self, 1948, 12, (4, 7, 7, 7, 6))
check_weeks(self, 1927, 12, (3, 7, 7, 7, 7))
check_weeks(self, 1995, 12, (2, 7, 7, 7, 7, 1))
end

mutable struct TimegmTestCase <: AbstractTimegmTestCase
TIMESTAMPS::Vector{Int64}

                    TimegmTestCase(TIMESTAMPS::Vector{Int64} = [0, 10, 100, 1000, 10000, 100000, 1000000, 1234567890, 1262304000, 1275785153]) =
                        new(TIMESTAMPS)
end
function test_timegm(self::TimegmTestCase)
for secs in self.TIMESTAMPS
tuple = gmtime(time, secs)
@test (secs == timegm(calendar, tuple))
end
end

mutable struct MonthRangeTestCase <: AbstractMonthRangeTestCase

end
function test_january(self::MonthRangeTestCase)
@test (monthrange(calendar, 2004, 1) == (3, 31))
end

function test_february_leap(self::MonthRangeTestCase)
@test (monthrange(calendar, 2004, 2) == (6, 29))
end

function test_february_nonleap(self::MonthRangeTestCase)
@test (monthrange(calendar, 2010, 2) == (0, 28))
end

function test_december(self::MonthRangeTestCase)
@test (monthrange(calendar, 2004, 12) == (2, 31))
end

function test_zeroth_month(self::MonthRangeTestCase)
assertRaises(self, calendar.IllegalMonthError) do 
monthrange(calendar, 2004, 0)
end
end

function test_thirteenth_month(self::MonthRangeTestCase)
assertRaises(self, calendar.IllegalMonthError) do 
monthrange(calendar, 2004, 13)
end
end

function test_illegal_month_reported(self::MonthRangeTestCase)
assertRaisesRegex(self, calendar.IllegalMonthError, "65") do 
monthrange(calendar, 2004, 65)
end
end

mutable struct LeapdaysTestCase <: AbstractLeapdaysTestCase

end
function test_no_range(self::LeapdaysTestCase)
@test (leapdays(calendar, 2010, 2010) == 0)
end

function test_no_leapdays(self::LeapdaysTestCase)
@test (leapdays(calendar, 2010, 2011) == 0)
end

function test_no_leapdays_upper_boundary(self::LeapdaysTestCase)
@test (leapdays(calendar, 2010, 2012) == 0)
end

function test_one_leapday_lower_boundary(self::LeapdaysTestCase)
@test (leapdays(calendar, 2012, 2013) == 1)
end

function test_several_leapyears_in_range(self::LeapdaysTestCase)
@test (leapdays(calendar, 1997, 2020) == 5)
end

function conv(s)
return Vector{UInt8}(replace(s, "\n", os.linesep))
end

mutable struct CommandLineTestCase <: AbstractCommandLineTestCase

end
function run_ok(self::CommandLineTestCase)
return assert_python_ok("-m", "calendar", args...)[2]
end

function assertFailure(self::CommandLineTestCase)
rc, stdout, stderr = assert_python_failure("-m", "calendar", args...)
assertIn(self, b"usage:", stderr)
@test (rc == 2)
end

function test_help(self::CommandLineTestCase)
stdout = run_ok(self)
assertIn(self, b"usage:", stdout)
assertIn(self, b"calendar.py", stdout)
assertIn(self, b"--help", stdout)
end

function test_illegal_arguments(self::CommandLineTestCase)
assertFailure(self)
assertFailure(self)
assertFailure(self)
assertFailure(self)
end

function test_output_current_year(self::CommandLineTestCase)
stdout = run_ok(self)
year = now(datetime.datetime).year
assertIn(self, Vector{UInt8}(" %s" % year), stdout)
assertIn(self, b"January", stdout)
assertIn(self, b"Mo Tu We Th Fr Sa Su", stdout)
end

function test_output_year(self::CommandLineTestCase)
stdout = run_ok(self)
@test (stdout == conv(result_2004_text))
end

function test_output_month(self::CommandLineTestCase)
stdout = run_ok(self)
@test (stdout == conv(result_2004_01_text))
end

function test_option_encoding(self::CommandLineTestCase)
assertFailure(self)
assertFailure(self)
stdout = run_ok(self)
@test (stdout == Vector{UInt8}(result_2004_text))
end

function test_option_locale(self::CommandLineTestCase)
assertFailure(self)
assertFailure(self)
assertFailure(self)
lang, enc = getdefaultlocale(locale)
lang = lang || "C"
enc = enc || "UTF-8"
try
oldlocale = getlocale(locale, locale.LC_TIME)
try
setlocale(locale, locale.LC_TIME, (lang, enc))
finally
setlocale(locale, locale.LC_TIME, oldlocale)
end
catch exn
if exn isa (locale.Error, ValueError)
skipTest(self, "cannot set the system default locale")
end
end
stdout = run_ok(self)
assertIn(self, Vector{UInt8}("2004"), stdout)
end

function test_option_width(self::CommandLineTestCase)
assertFailure(self)
assertFailure(self)
assertFailure(self)
stdout = run_ok(self)
assertIn(self, b"Mon Tue Wed Thu Fri Sat Sun", stdout)
end

function test_option_lines(self::CommandLineTestCase)
assertFailure(self)
assertFailure(self)
assertFailure(self)
stdout = run_ok(self)
assertIn(self, conv("December\n\nMo Tu We"), stdout)
end

function test_option_spacing(self::CommandLineTestCase)
assertFailure(self)
assertFailure(self)
assertFailure(self)
stdout = run_ok(self)
assertIn(self, b"Su        Mo", stdout)
end

function test_option_months(self::CommandLineTestCase)
assertFailure(self)
assertFailure(self)
assertFailure(self)
stdout = run_ok(self)
assertIn(self, conv("\nMo Tu We Th Fr Sa Su\n"), stdout)
end

function test_option_type(self::CommandLineTestCase)
assertFailure(self)
assertFailure(self)
assertFailure(self)
stdout = run_ok(self)
@test (stdout == conv(result_2004_text))
stdout = run_ok(self)
@test (stdout[begin:6] == b"<?xml ")
assertIn(self, b"<title>Calendar for 2004</title>", stdout)
end

function test_html_output_current_year(self::CommandLineTestCase)
stdout = run_ok(self)
year = now(datetime.datetime).year
assertIn(self, Vector{UInt8}("<title>Calendar for %s</title>" % year), stdout)
assertIn(self, b"<tr><th colspan=\"7\" class=\"month\">January</th></tr>", stdout)
end

function test_html_output_year_encoding(self::CommandLineTestCase)
stdout = run_ok(self)
@test (stdout == Vector{UInt8}(result_2004_html))
end

function test_html_output_year_css(self::CommandLineTestCase)
assertFailure(self)
assertFailure(self)
stdout = run_ok(self)
assertIn(self, b"<link rel=\"stylesheet\" type=\"text/css\" href=\"custom.css\" />", stdout)
end

mutable struct MiscTestCase <: AbstractMiscTestCase

end
function test__all__(self::MiscTestCase)
not_exported = Set(["mdays", "January", "February", "EPOCH", "different_locale", "c", "prweek", "week", "format", "formatstring", "main", "monthlen", "prevmonth", "nextmonth"])
check__all__(support, self, calendar, not_exported)
end

mutable struct TestSubClassingCase <: AbstractTestSubClassingCase
cal::CustomHTMLCal
cssclass_month::String
cssclass_month_head::String
cssclass_year::String
cssclass_year_head::String
cssclasses
cssclasses_weekday_head::Vector{String}

                    TestSubClassingCase(cal::CustomHTMLCal, cssclass_month::String = "text-center month", cssclass_month_head::String = "text-center month-head", cssclass_year::String = "text-italic ", cssclass_year_head::String = "lead ", cssclasses = [style + " text-nowrap" for style in calendar.HTMLCalendar.cssclasses], cssclasses_weekday_head::Vector{String} = ["red", "blue", "green", "lilac", "yellow", "orange", "pink"]) =
                        new(cal, cssclass_month, cssclass_month_head, cssclass_year, cssclass_year_head, cssclasses, cssclasses_weekday_head)
end
function setUp(self::CustomHTMLCal)
mutable struct CustomHTMLCal <: AbstractCustomHTMLCal
cssclass_month::String
cssclass_month_head::String
cssclass_year::String
cssclass_year_head::String
cssclasses
cssclasses_weekday_head::Vector{String}

                    CustomHTMLCal(cssclass_month::String = "text-center month", cssclass_month_head::String = "text-center month-head", cssclass_year::String = "text-italic ", cssclass_year_head::String = "lead ", cssclasses = [style + " text-nowrap" for style in calendar.HTMLCalendar.cssclasses], cssclasses_weekday_head::Vector{String} = ["red", "blue", "green", "lilac", "yellow", "orange", "pink"]) =
                        new(cssclass_month, cssclass_month_head, cssclass_year, cssclass_year_head, cssclasses, cssclasses_weekday_head)
end

self.cal = CustomHTMLCal()
end

function test_formatmonthname(self::TestSubClassingCase)
assertIn(self, "class=\"text-center month-head\"", formatmonthname(self.cal, 2017, 5))
end

function test_formatmonth(self::TestSubClassingCase)
assertIn(self, "class=\"text-center month\"", formatmonth(self.cal, 2017, 5))
end

function test_formatweek(self::TestSubClassingCase)
weeks = monthdays2calendar(self.cal, 2017, 5)
assertIn(self, "class=\"wed text-nowrap\"", formatweek(self.cal, weeks[1]))
end

function test_formatweek_head(self::TestSubClassingCase)
header = formatweekheader(self.cal)
for color in self.cal.cssclasses_weekday_head
assertIn(self, "<th class=\"%s\">" % color, header)
end
end

function test_format_year(self::TestSubClassingCase)
assertIn(self, "<table border=\"0\" cellpadding=\"0\" cellspacing=\"0\" class=\"%s\">" % self.cal.cssclass_year, formatyear(self.cal, 2017))
end

function test_format_year_head(self::TestSubClassingCase)
assertIn(self, "<tr><th colspan=\"%d\" class=\"%s\">%s</th></tr>" % (3, self.cal.cssclass_year_head, 2017), formatyear(self.cal, 2017))
end

function main()
output_test_case = OutputTestCase()
normalize_calendar(output_test_case)
check_htmlcalendar_encoding(output_test_case)
test_output(output_test_case)
test_output_textcalendar(output_test_case)
test_output_htmlcalendar_encoding_ascii(output_test_case)
test_output_htmlcalendar_encoding_utf8(output_test_case)
test_output_htmlcalendar_encoding_default(output_test_case)
test_yeardatescalendar(output_test_case)
test_yeardayscalendar(output_test_case)
test_formatweekheader_short(output_test_case)
test_formatweekheader_long(output_test_case)
test_formatmonth(output_test_case)
test_formatmonthname_with_year(output_test_case)
test_formatmonthname_without_year(output_test_case)
test_prweek(output_test_case)
test_prmonth(output_test_case)
test_pryear(output_test_case)
test_format(output_test_case)
calendar_test_case = CalendarTestCase()
test_isleap(calendar_test_case)
test_setfirstweekday(calendar_test_case)
test_illegal_weekday_reported(calendar_test_case)
test_enumerate_weekdays(calendar_test_case)
test_days(calendar_test_case)
test_months(calendar_test_case)
test_locale_calendars(calendar_test_case)
test_locale_html_calendar_custom_css_class_month_name(calendar_test_case)
test_locale_html_calendar_custom_css_class_weekday(calendar_test_case)
test_itermonthdays3(calendar_test_case)
test_itermonthdays4(calendar_test_case)
test_itermonthdays(calendar_test_case)
test_itermonthdays2(calendar_test_case)
month_calendar_test_case = MonthCalendarTestCase()
setUp(month_calendar_test_case)
tearDown(month_calendar_test_case)
check_weeks(month_calendar_test_case)
timegm_test_case = TimegmTestCase()
test_timegm(timegm_test_case)
month_range_test_case = MonthRangeTestCase()
test_january(month_range_test_case)
test_february_leap(month_range_test_case)
test_february_nonleap(month_range_test_case)
test_december(month_range_test_case)
test_zeroth_month(month_range_test_case)
test_thirteenth_month(month_range_test_case)
test_illegal_month_reported(month_range_test_case)
leapdays_test_case = LeapdaysTestCase()
test_no_range(leapdays_test_case)
test_no_leapdays(leapdays_test_case)
test_no_leapdays_upper_boundary(leapdays_test_case)
test_one_leapday_lower_boundary(leapdays_test_case)
test_several_leapyears_in_range(leapdays_test_case)
command_line_test_case = CommandLineTestCase()
run_ok(command_line_test_case)
assertFailure(command_line_test_case)
test_help(command_line_test_case)
test_illegal_arguments(command_line_test_case)
test_output_current_year(command_line_test_case)
test_output_year(command_line_test_case)
test_output_month(command_line_test_case)
test_option_encoding(command_line_test_case)
test_option_locale(command_line_test_case)
test_option_width(command_line_test_case)
test_option_lines(command_line_test_case)
test_option_spacing(command_line_test_case)
test_option_months(command_line_test_case)
test_option_type(command_line_test_case)
test_html_output_current_year(command_line_test_case)
test_html_output_year_encoding(command_line_test_case)
test_html_output_year_css(command_line_test_case)
misc_test_case = MiscTestCase()
test__all__(misc_test_case)
test_sub_classing_case = TestSubClassingCase()
setUp(test_sub_classing_case)
test_formatmonthname(test_sub_classing_case)
test_formatmonth(test_sub_classing_case)
test_formatweek(test_sub_classing_case)
test_formatweek_head(test_sub_classing_case)
test_format_year(test_sub_classing_case)
test_format_year_head(test_sub_classing_case)
end

main()