-- phpMyAdmin SQL Dump
-- version 4.0.10deb1
-- http://www.phpmyadmin.net
--
-- Host: localhost
-- Generation Time: Feb 11, 2016 at 11:49 AM
-- Server version: 5.5.47-0ubuntu0.14.04.1
-- PHP Version: 5.5.9-1ubuntu4.14

SET SQL_MODE = "NO_AUTO_VALUE_ON_ZERO";
SET time_zone = "+00:00";


/*!40101 SET @OLD_CHARACTER_SET_CLIENT=@@CHARACTER_SET_CLIENT */;
/*!40101 SET @OLD_CHARACTER_SET_RESULTS=@@CHARACTER_SET_RESULTS */;
/*!40101 SET @OLD_COLLATION_CONNECTION=@@COLLATION_CONNECTION */;
/*!40101 SET NAMES utf8 */;

--
-- Database: `library`
--

-- --------------------------------------------------------

--
-- Table structure for table `about_publishing`
--

CREATE TABLE IF NOT EXISTS `about_publishing` (
  `publishing_house` varchar(30) NOT NULL,
  `country` varchar(30) NOT NULL,
  `city` varchar(30) NOT NULL,
  `phone` varchar(15) NOT NULL,
  PRIMARY KEY (`publishing_house`),
  KEY `city` (`city`)
) ENGINE=InnoDB DEFAULT CHARSET=utf8;

--
-- Dumping data for table `about_publishing`
--

INSERT INTO `about_publishing` (`publishing_house`, `country`, `city`, `phone`) VALUES
('Barvinok', 'Ukraine', 'Kiev', '418-324-12-42'),
('KojimaProductions', 'Japan', 'Tokyo', '461-615-57-23'),
('Polska', 'Poland', 'Krakov', '120-435-12-10'),
('Rosman', 'Russia', 'Moscow', '285-325-21-51');

-- --------------------------------------------------------

--
-- Table structure for table `data`
--

CREATE TABLE IF NOT EXISTS `data` (
  `book_name` varchar(50) NOT NULL,
  `author` varchar(30) NOT NULL,
  `publishing_year` int(11) NOT NULL,
  `publishing_house` varchar(30) NOT NULL,
  `price` float NOT NULL,
  `count_of_books` int(11) NOT NULL,
  PRIMARY KEY (`book_name`)
) ENGINE=InnoDB DEFAULT CHARSET=utf8;

--
-- Dumping data for table `data`
--

INSERT INTO `data` (`book_name`, `author`, `publishing_year`, `publishing_house`, `price`, `count_of_books`) VALUES
('Harry potter', 'Rowling', 1996, 'Rosman', 2.1, 240),
('Lord of the rings', 'Tolkien', 1958, 'Rosman', 2.5, 100),
('The witcher', 'Spkovskiy', 1987, 'Polska', 2.7, 100);

-- --------------------------------------------------------

--
-- Table structure for table `directory_of_cities`
--

CREATE TABLE IF NOT EXISTS `directory_of_cities` (
  `city` varchar(30) NOT NULL,
  `country` varchar(30) NOT NULL,
  PRIMARY KEY (`city`),
  UNIQUE KEY `city_2` (`city`),
  KEY `city` (`city`)
) ENGINE=InnoDB DEFAULT CHARSET=utf8;

--
-- Dumping data for table `directory_of_cities`
--

INSERT INTO `directory_of_cities` (`city`, `country`) VALUES
('Kiev', 'Ukraine'),
('Krakov', 'Poland'),
('Moscow', 'Russia'),
('Tokyo', 'Japan');

--
-- Constraints for dumped tables
--

--
-- Constraints for table `about_publishing`
--
ALTER TABLE `about_publishing`
  ADD CONSTRAINT `about_publishing_ibfk_1` FOREIGN KEY (`city`) REFERENCES `directory_of_cities` (`city`);

/*!40101 SET CHARACTER_SET_CLIENT=@OLD_CHARACTER_SET_CLIENT */;
/*!40101 SET CHARACTER_SET_RESULTS=@OLD_CHARACTER_SET_RESULTS */;
/*!40101 SET COLLATION_CONNECTION=@OLD_COLLATION_CONNECTION */;
